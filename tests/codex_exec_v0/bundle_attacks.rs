use super::*;
use legitimacy::trajectory::codex_exec_v0::{AdapterErrorCodeV0, InspectedPrivateAdapterBundleV0};
use legitimacy::{
    EvidenceV0, EvidencedV0, TrajectoryTraceV0, TrajectoryValidationContextV0, artifact_digest_v0,
    trajectory_digest_v0,
};
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;

#[derive(Clone, Copy, Debug)]
enum BundleMutationOutcome {
    Inspect(AdapterErrorCodeV0),
    Revalidate(AdapterErrorCodeV0),
}

struct BundleMutation {
    name: &'static str,
    mutate: fn(&mut serde_json::Value),
    expected: BundleMutationOutcome,
}

#[test]
fn transformation_manifest_rejects_missing_extra_duplicate_reordered_and_field_attacks() {
    let authority = synthetic_authority(COMPLETED);
    let context = trusted(&authority);
    let original = private_bundle_value(&authority, &context);
    use BundleMutationOutcome::{Inspect, Revalidate};
    let mutations = [
        BundleMutation {
            name: "missing manifest entry",
            mutate: |value| {
                value["payload_manifest"].as_array_mut().unwrap().remove(0);
            },
            expected: Revalidate(AdapterErrorCodeV0::BundleMismatch),
        },
        BundleMutation {
            name: "extra manifest entry",
            mutate: |value| {
                value["payload_manifest"]
                    .as_array_mut()
                    .unwrap()
                    .push(serde_json::json!({
                        "role":"official-trace-json",
                        "format":"trajectory-v0-compact-json",
                        "ordinal":2,
                        "byte_length":0,
                        "digest":zero_digest()
                    }));
            },
            expected: Revalidate(AdapterErrorCodeV0::BundleMismatch),
        },
        BundleMutation {
            name: "duplicate manifest entry",
            mutate: |value| {
                let duplicate = value["payload_manifest"][0].clone();
                value["payload_manifest"]
                    .as_array_mut()
                    .unwrap()
                    .push(duplicate);
            },
            expected: Revalidate(AdapterErrorCodeV0::BundleMismatch),
        },
        BundleMutation {
            name: "reordered manifest entries",
            mutate: |value| value["payload_manifest"].as_array_mut().unwrap().swap(0, 1),
            expected: Revalidate(AdapterErrorCodeV0::BundleMismatch),
        },
        BundleMutation {
            name: "unknown component role",
            mutate: |value| {
                value["payload_manifest"][0]["role"] = serde_json::json!("unknown-role");
            },
            expected: Inspect(AdapterErrorCodeV0::JsonShape),
        },
        BundleMutation {
            name: "unknown component format",
            mutate: |value| {
                value["payload_manifest"][0]["format"] = serde_json::json!("unknown-format");
            },
            expected: Inspect(AdapterErrorCodeV0::JsonShape),
        },
        BundleMutation {
            name: "incorrect component ordinal",
            mutate: |value| {
                value["payload_manifest"][0]["ordinal"] = serde_json::json!(9);
            },
            expected: Revalidate(AdapterErrorCodeV0::BundleMismatch),
        },
        BundleMutation {
            name: "incorrect component length",
            mutate: |value| {
                value["payload_manifest"][0]["byte_length"] = serde_json::json!(1);
            },
            expected: Revalidate(AdapterErrorCodeV0::BundleMismatch),
        },
        BundleMutation {
            name: "incorrect component digest",
            mutate: |value| {
                value["payload_manifest"][0]["digest"] = serde_json::json!(zero_digest());
            },
            expected: Revalidate(AdapterErrorCodeV0::BundleMismatch),
        },
    ];
    assert_eq!(mutations.len(), 9);
    for mutation in &mutations {
        let mut value = original.clone();
        (mutation.mutate)(&mut value);
        value["transformation_receipt"]["payload_manifest"] = value["payload_manifest"].clone();
        assert_bundle_mutation_rejected(
            &original,
            value,
            &authority,
            &context,
            mutation.name,
            mutation.expected,
        );
    }
}

#[test]
fn complete_regeneration_rejects_locally_valid_attacker_rehashed_trace_surfaces() {
    let authority = synthetic_authority(COMPLETED);
    let context = trusted(&authority);
    let base = private_bundle_value(&authority, &context);
    let mutations = [
        (
            "run identifier",
            (|trace: &mut serde_json::Value| {
                trace["run_id"]["value"] = serde_json::json!("run-attacker");
            }) as fn(&mut serde_json::Value),
        ),
        ("event identifier", |trace: &mut serde_json::Value| {
            trace["events"][0]["event_id"]["value"] = serde_json::json!("event-attacker");
        }),
        ("event kind", |trace: &mut serde_json::Value| {
            trace["events"][0]["kind"]["value"] = serde_json::json!("observation");
        }),
        ("terminal status", |trace: &mut serde_json::Value| {
            trace["events"][4]["payload"]["source-status"]["value"]["value"] =
                serde_json::json!("completed");
        }),
        ("source event payload", |trace: &mut serde_json::Value| {
            trace["events"][0]["payload"]["source-event"]["value"]["value"] =
                serde_json::json!("attacker-event");
        }),
        ("derivation rule", |trace: &mut serde_json::Value| {
            trace["events"][1]["event_id"]["evidence"]["rule"] = serde_json::json!({
                "identity":"derivation.attacker",
                "version":"0",
                "hash":artifact_digest_v0(b"attacker derivation")
            });
        }),
        ("source locator", |trace: &mut serde_json::Value| {
            let locator = trace["run_id"]["evidence"]["source_inputs"][0].clone();
            trace["events"][4]["sequence_index"]["evidence"]["source_inputs"][0] = locator;
        }),
    ];

    for (name, mutate) in mutations {
        let mut bundle = base.clone();
        let mut trace_json: serde_json::Value =
            serde_json::from_str(bundle["official_trace_json"].as_str().unwrap()).unwrap();
        mutate(&mut trace_json);
        make_attacker_bundle_internally_consistent(&mut bundle, trace_json);
        assert_bundle_mutation_rejected(
            &base,
            bundle,
            &authority,
            &context,
            name,
            BundleMutationOutcome::Revalidate(AdapterErrorCodeV0::BundleMismatch),
        );
    }
}

fn assert_bundle_mutation_rejected(
    original: &serde_json::Value,
    mutated: serde_json::Value,
    authority: &InputAuthorityReceiptV0,
    context: &TrustedAdaptationContextV0,
    name: &str,
    expected: BundleMutationOutcome,
) {
    assert_ne!(&mutated, original, "{name}");
    let mut bytes = serde_json::to_vec(&mutated).unwrap();
    bytes.push(b'\n');
    match expected {
        BundleMutationOutcome::Inspect(code) => {
            assert_eq!(
                InspectedPrivateAdapterBundleV0::from_json_slice(&bytes)
                    .expect_err("declared inspection rejection")
                    .code(),
                code,
                "{name}"
            );
        }
        BundleMutationOutcome::Revalidate(code) => {
            let inspected = InspectedPrivateAdapterBundleV0::from_json_slice(&bytes)
                .expect("declared inspection success");
            assert_eq!(
                inspected
                    .revalidate(COMPLETED, authority, context)
                    .expect_err("declared revalidation rejection")
                    .code(),
                code,
                "{name}"
            );
        }
    }
}

fn make_attacker_bundle_internally_consistent(
    bundle: &mut serde_json::Value,
    trace_json: serde_json::Value,
) {
    let encoded = serde_json::to_vec(&trace_json).unwrap();
    let trace = TrajectoryTraceV0::from_json_slice(&encoded).unwrap();
    let records = COMPLETED
        .strip_suffix(b"\n")
        .unwrap()
        .split(|byte| *byte == b'\n')
        .collect::<Vec<_>>();
    let trusted = TrajectoryValidationContextV0 {
        adapter: trace.adapter.clone(),
        policy: trace.policy.clone(),
        raw_capture: trace.raw_capture.clone(),
        allowed_derivations: derivation_rules(&trace),
    };
    let validated = trace.validate(&records, &trusted).unwrap();
    let compact = validated.to_compact_json().unwrap();
    let canonical = validated.canonical_bytes();
    let digest = trajectory_digest_v0(&validated);
    bundle["official_trace_json"] =
        serde_json::Value::String(String::from_utf8(compact.clone()).unwrap());
    bundle["canonical_trace_lower_hex"] = serde_json::Value::String(lower_hex(&canonical));
    bundle["trajectory_digest"] = serde_json::Value::String(digest.clone());
    bundle["payload_manifest"] = serde_json::json!([
        {
            "role":"official-trace-json",
            "format":"trajectory-v0-compact-json",
            "ordinal":0,
            "byte_length":compact.len(),
            "digest":component_digest("official-trace-json", &compact)
        },
        {
            "role":"canonical-trace",
            "format":"trajectory-v0-canonical-bytes",
            "ordinal":1,
            "byte_length":canonical.len(),
            "digest":component_digest("canonical-trace", &canonical)
        }
    ]);
    bundle["transformation_receipt"]["normalized_trace_digest"] = serde_json::Value::String(digest);
    bundle["transformation_receipt"]["payload_manifest"] = bundle["payload_manifest"].clone();
}

fn derivation_rules(trace: &TrajectoryTraceV0) -> BTreeSet<legitimacy::ArtifactBindingV0> {
    let mut rules = BTreeSet::new();
    add_rule(&trace.run_id, &mut rules);
    for event in &trace.events {
        add_rule(&event.event_id, &mut rules);
        add_rule(&event.sequence_index, &mut rules);
        add_rule(&event.kind, &mut rules);
        if let Some(source_item_id) = &event.source_item_id {
            add_rule(source_item_id, &mut rules);
        }
        for value in event.payload.values() {
            add_rule(value, &mut rules);
        }
    }
    rules
}

fn add_rule<T>(value: &EvidencedV0<T>, rules: &mut BTreeSet<legitimacy::ArtifactBindingV0>) {
    if let EvidenceV0::DeclaredDerivationBinding { rule, .. } = &value.evidence {
        rules.insert(rule.clone());
    }
}

fn private_bundle_value(
    authority: &InputAuthorityReceiptV0,
    context: &TrustedAdaptationContextV0,
) -> serde_json::Value {
    let bytes = adapt_codex_exec_v0(COMPLETED, authority, context)
        .unwrap()
        .to_private_bundle()
        .unwrap()
        .to_json_line()
        .unwrap();
    serde_json::from_slice(&bytes).unwrap()
}

fn component_digest(role: &str, bytes: &[u8]) -> String {
    framed_hash(
        &format!("legitimacy.codex-exec-v0.payload-component.{role}.v0"),
        &[bytes],
    )
}

fn framed_hash(domain: &str, components: &[&[u8]]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(b"legitimacy.trajectory.hash.v0\0");
    frame(&mut hasher, domain.as_bytes());
    hasher.update(u64::try_from(components.len()).unwrap().to_be_bytes());
    for component in components {
        frame(&mut hasher, component);
    }
    format!("sha256:{:x}", hasher.finalize())
}

fn frame(hasher: &mut Sha256, bytes: &[u8]) {
    hasher.update(u64::try_from(bytes.len()).unwrap().to_be_bytes());
    hasher.update(bytes);
}

fn lower_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn zero_digest() -> &'static str {
    "sha256:0000000000000000000000000000000000000000000000000000000000000000"
}
