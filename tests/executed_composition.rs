use legitimacy::executed_composition::{self as e, Channel, Decision, Knowledge, Payload};

type RunMutation = Box<dyn Fn(&mut e::Run)>;

const BUNDLE: &[u8] = include_bytes!("../fixtures/executed-composition-v1/capture/bundle.json");
const TRUST: &[u8] =
    include_bytes!("../fixtures/executed-composition-v1/capture/trust-policy.json");

#[test]
fn exhaustive_lean_table_matches_conventional_full_context_semantics() {
    for state in 0..4 {
        for actor in 0..2 {
            for payload in [Payload::Fragment, Payload::Summary] {
                for channel in [Channel::Public, Channel::Vault] {
                    for auth in [false, true] {
                        for scope in [false, true] {
                            let row = e::transition(state, actor, payload, channel, auth, scope);
                            let after =
                                if payload == Payload::Fragment && channel == Channel::Public {
                                    state | if actor == 0 { 2 } else { 1 }
                                } else {
                                    state
                                };
                            let local = auth && scope;
                            let repaired = local && after != 3;
                            assert_eq!(row[1], usize::from(local));
                            assert_eq!(row[2], usize::from(repaired));
                            assert_eq!(row[3], if local { after } else { state });
                            assert_eq!(row[4], if repaired { after } else { state });
                            if state != 3 {
                                assert_ne!(row[4], 3);
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn executed_control_and_useful_same_property_repair() {
    let runs = e::suite();
    assert!(
        runs.iter()
            .all(|r| r.events.len() == 2 && r.policy == e::POLICY)
    );
    let reports: Vec<_> = runs.iter().map(e::check).collect();
    assert_eq!(reports[0].knowledge, Knowledge::Violated);
    assert_eq!(reports[0].per_call_baseline, Decision::Permit);
    assert_eq!(reports[0].participating_events, [0, 1]);
    assert_eq!(reports[0].first_forbidden_event, Some(1));
    for i in [1, 3, 4] {
        assert_eq!(reports[i].knowledge, Knowledge::Safe);
        assert_eq!(reports[i].governance, Decision::Permit);
        assert!(
            runs[i]
                .events
                .iter()
                .all(|event| !event.effect.as_ref().unwrap().is_empty())
        );
    }
    assert_eq!(reports[2].knowledge, Knowledge::Safe);
    assert_eq!(reports[2].governance, Decision::Deny);
    assert_eq!(reports[5].governance, Decision::Deny);
    assert!(
        runs[5]
            .events
            .iter()
            .all(|ev| ev.authenticated == Some(true))
    );
    assert_eq!(reports[6].knowledge, Knowledge::Inconclusive);
    assert_eq!(reports[6].governance, Decision::Review);
    assert!(
        reports
            .iter()
            .all(|r| r.governance == r.full_context_baseline)
    );
}

#[test]
fn signed_execution_uses_existing_replay_authority_and_preserves_missing_scope() {
    let signed = e::parse_bundle(BUNDLE).unwrap();
    for run in &signed {
        let report = e::check_signed(run, TRUST);
        assert!(report.capture_authenticated);
        assert_ne!(report.knowledge, Knowledge::Invalid);
    }
    let denied = e::check_signed(&signed[5], TRUST);
    assert!(denied.capture_authenticated);
    assert_eq!(denied.governance, Decision::Deny);
    let missing = e::check_signed(&signed[6], TRUST);
    assert!(missing.capture_authenticated);
    assert_eq!(missing.knowledge, Knowledge::Inconclusive);
    let expected: Vec<e::Report> = serde_json::from_slice(include_bytes!(
        "../fixtures/executed-composition-v1/capture/reports.json"
    ))
    .unwrap();
    assert_eq!(
        signed
            .iter()
            .map(|s| e::check_signed(s, TRUST))
            .collect::<Vec<_>>(),
        expected
    );
}

#[test]
fn load_bearing_evidence_never_defaults_to_safe() {
    let run = e::suite()[3].clone();
    let mutations: Vec<RunMutation> = vec![
        Box::new(|r| r.grants = None),
        Box::new(|r| r.principals = None),
        Box::new(|r| r.public_sink = None),
        Box::new(|r| r.vault_sink = None),
        Box::new(|r| r.complete = false),
        Box::new(|r| r.events[0].principal = None),
        Box::new(|r| r.events[0].authenticated = None),
        Box::new(|r| r.events[0].channel = None),
        Box::new(|r| r.events[0].payload = None),
        Box::new(|r| r.events[0].effect = None),
    ];
    for mutate in mutations {
        let mut changed = run.clone();
        mutate(&mut changed);
        assert_eq!(e::check(&changed).knowledge, Knowledge::Inconclusive);
        assert_eq!(e::check(&changed).governance, Decision::Review);
    }
}

#[test]
fn semantic_mutations_reject_fabricated_effects_scope_order_and_property() {
    let run = e::suite()[3].clone();
    let mutations: Vec<RunMutation> = vec![
        Box::new(|r| {
            r.policy = r
                .policy
                .replace("boolJointForbiddenList", "boolTrackedSafeForbiddenList")
        }),
        Box::new(|r| r.events[0].effect = Some("fabricated".into())),
        Box::new(|r| r.events[0].index = 1),
        Box::new(|r| r.events.swap(0, 1)),
        Box::new(|r| r.events[0].principal = Some("undeclared".into())),
        Box::new(|r| r.principals.as_mut().unwrap()[1] = "principal-A".into()),
        Box::new(|r| r.grants.as_mut().unwrap().clear()),
        Box::new(|r| {
            for g in r.grants.as_mut().unwrap() {
                g.task = "other-task".into();
            }
        }),
        Box::new(|r| r.events[1].channel = Some(Channel::Public)),
        Box::new(|r| {
            r.public_sink
                .as_mut()
                .unwrap()
                .push("hidden-delivery".into())
        }),
    ];
    for mutate in mutations {
        let mut changed = run.clone();
        mutate(&mut changed);
        assert_eq!(e::check(&changed).knowledge, Knowledge::Invalid);
    }
    let mut denied = e::suite()[2].clone();
    denied.events[1].effect = Some("SYNTHETIC-BETA".into());
    assert_eq!(e::check(&denied).knowledge, Knowledge::Invalid);
}

#[test]
fn presentation_renaming_does_not_change_semantics() {
    for mut run in e::suite().into_iter().take(6) {
        let original = e::check(&run);
        run.id = "</script><img src=x onerror=alert(1)>".into();
        let new = ["renamed-X", "renamed-Y"];
        let old = run.principals.clone().unwrap();
        for (i, value) in new.iter().enumerate() {
            run.principals.as_mut().unwrap()[i] = (*value).into();
            for g in run.grants.as_mut().unwrap() {
                if g.principal == old[i] {
                    g.principal = (*value).into();
                }
            }
            for event in &mut run.events {
                if event.principal.as_ref() == Some(&old[i]) {
                    event.principal = Some((*value).into());
                }
            }
        }
        let actual = e::check(&run);
        assert_eq!(actual.knowledge, original.knowledge);
        assert_eq!(actual.governance, original.governance);
        assert_eq!(actual.exposure, original.exposure);
    }
}

#[test]
fn signature_and_wire_mutations_are_rejected() {
    let signed = e::parse_bundle(BUNDLE).unwrap();
    let mut changed = signed[0].clone();
    changed.run.events[0].effect = Some("different".into());
    assert_eq!(
        e::check_signed(&changed, TRUST).knowledge,
        Knowledge::Invalid
    );
    let mut changed = signed[0].clone();
    changed.receipt["authority_epoch"] = 2.into();
    assert!(!e::check_signed(&changed, TRUST).capture_authenticated);
    let mut changed = signed[0].clone();
    changed.run = signed[1].run.clone();
    assert_eq!(
        e::check_signed(&changed, TRUST).knowledge,
        Knowledge::Invalid
    );
    let wire = String::from_utf8(BUNDLE.to_vec()).unwrap();
    let duplicate = wire.replacen(
        "\"authority_epoch\":1",
        "\"authority_epoch\":1,\"authority_epoch\":1",
        1,
    );
    assert_ne!(wire, duplicate);
    assert!(e::parse_bundle(duplicate.as_bytes()).is_err());
    let escaped_duplicate = wire.replacen(
        "\"authority_epoch\":1",
        "\"authority_epoch\":1,\"authority_\\u0065poch\":1",
        1,
    );
    assert!(e::parse_bundle(escaped_duplicate.as_bytes()).is_err());
    assert!(e::parse_bundle(&vec![b' '; e::MAX_BYTES as usize + 1]).is_err());
    assert!(e::parse_bundle(b"[]").is_err());
}

#[test]
fn cli_recomputes_signed_results_and_rejects_nonregular_inputs() {
    use std::process::Command;
    let binary = env!("CARGO_BIN_EXE_legitimacy-executed-composition");
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let fixture = root.join("fixtures/executed-composition-v1/capture");
    let output = Command::new(binary)
        .arg("check")
        .arg(fixture.join("bundle.json"))
        .arg("--trust")
        .arg(fixture.join("trust-policy.json"))
        .output()
        .unwrap();
    assert!(output.status.success());
    let reports: Vec<e::Report> = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(reports[0].knowledge, Knowledge::Violated);
    assert_eq!(reports[6].knowledge, Knowledge::Inconclusive);
    let output = Command::new(binary)
        .arg("check")
        .arg(&fixture)
        .arg("--trust")
        .arg(fixture.join("trust-policy.json"))
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    #[cfg(unix)]
    {
        let fifo =
            std::env::temp_dir().join(format!("legitimacy-executed-fifo-{}", uuid::Uuid::new_v4()));
        assert!(
            Command::new("mkfifo")
                .arg(&fifo)
                .status()
                .unwrap()
                .success()
        );
        let output = Command::new(binary)
            .arg("check")
            .arg(&fifo)
            .arg("--trust")
            .arg(fixture.join("trust-policy.json"))
            .output()
            .unwrap();
        std::fs::remove_file(fifo).unwrap();
        assert_eq!(output.status.code(), Some(2));
        assert!(
            String::from_utf8(output.stderr)
                .unwrap()
                .contains("regular file")
        );
    }
}
