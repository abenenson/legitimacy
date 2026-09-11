use super::*;

#[test]
fn rejects_malformed_or_mismatched_bindings_and_derivations() {
    let raw = vec![RECORD_ZERO];
    let (mut trace, declarations) = fixture(&raw);
    trace.schema.version = "1".to_string();
    assert_validation_error(
        &trace,
        &raw,
        &declarations,
        "schema identity, version, or hash",
    );

    let (mut trace, declarations) = fixture(&raw);
    trace.adapter.hash = "not-a-digest".to_string();
    assert_validation_error(&trace, &raw, &declarations, "must use 'sha256:' spelling");

    let (trace, mut declarations) = fixture(&raw);
    declarations.policy.version = "2".to_string();
    assert_validation_error(
        &trace,
        &raw,
        &declarations,
        "policy identity, version, or hash",
    );

    let (mut trace, declarations) = fixture(&raw);
    trace.events[0].sequence_index.evidence = EvidenceV0::DeclaredDerivationBinding {
        rule: binding("derivation.source-position", "1", b"other"),
        source_inputs: vec![locator(&raw, 0)],
    };
    assert_validation_error(
        &trace,
        &raw,
        &declarations,
        "undeclared derivation rule binding",
    );

    let (mut trace, declarations) = fixture(&raw);
    let rule = declarations
        .allowed_derivations
        .iter()
        .next()
        .unwrap()
        .clone();
    trace.events[0].sequence_index.evidence = EvidenceV0::DeclaredDerivationBinding {
        rule,
        source_inputs: Vec::new(),
    };
    assert_validation_error(&trace, &raw, &declarations, "no declared source inputs");
}

#[test]
fn referential_evidence_wire_names_reject_legacy_semantic_overclaims() {
    let raw = vec![RECORD_ZERO];
    let (trace, _) = fixture(&raw);
    let bytes = serde_json::to_vec(&trace).unwrap();
    let text = std::str::from_utf8(&bytes).unwrap();
    assert!(text.contains("cites-raw-range"));
    assert!(text.contains("declared-derivation-binding"));

    for (current, legacy) in [
        ("cites-raw-range", "raw-observed"),
        ("declared-derivation-binding", "derived-with-rule"),
    ] {
        let legacy_wire = text.replacen(current, legacy, 1);
        assert!(TrajectoryTraceV0::from_json_slice(legacy_wire.as_bytes()).is_err());
    }
}

#[test]
fn range_citation_explicitly_does_not_establish_semantic_entailment() {
    let raw = vec![RECORD_ZERO];
    let (trace, declarations) = fixture(&raw);
    let baseline = trace.validate(&raw, &declarations).unwrap();
    let baseline_digest = baseline.trajectory_digest();

    let mut changed = trace;
    changed.events[0].kind.value = Some(NormalizedEventKindV0::Message);
    let changed = changed.validate(&raw, &declarations).unwrap();
    assert_ne!(baseline_digest, changed.trajectory_digest());
}
