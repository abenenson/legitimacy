use std::{
    fs,
    path::PathBuf,
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

fn example_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join(name)
}

fn unique_path(label: &str, extension: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!("legitimacy-{label}-{nanos}.{extension}"))
}

#[test]
fn audit_events_reports_mixed_certified_and_rejected_rows() {
    let events_path = unique_path("audit-events-mixed", "jsonl");
    fs::write(
        &events_path,
        concat!(
            "{\"event_id\":\"evt-1\",\"claimant\":\"Read\",\"outcome\":1.0}\n",
            "{\"event_id\":\"evt-2\",\"claimant\":\"Bash\",\"outcome\":1.0}\n",
        ),
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .arg("audit")
        .arg(example_path("claude-agent-sdk-permissions.rule.toml"))
        .arg("--events")
        .arg(&events_path)
        .output()
        .unwrap();

    assert!(output.status.success(), "{output:?}");

    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["events_total"], 2);
    assert_eq!(report["certified"], 1);
    assert_eq!(report["rejected"], 1);

    let results = report["results"].as_array().unwrap();
    assert_eq!(results.len(), 2);

    assert_eq!(results[0]["event_id"], "evt-1");
    assert_eq!(results[0]["status"], "certified");
    assert_eq!(results[0]["certificate"]["claimant_id"], "Read");
    assert_eq!(results[0]["reason"], serde_json::Value::Null);

    assert_eq!(results[1]["event_id"], "evt-2");
    assert_eq!(results[1]["status"], "rejected");
    assert_eq!(results[1]["certificate"], serde_json::Value::Null);
    assert!(
        results[1]["reason"]
            .as_str()
            .unwrap()
            .contains("certificate outcome mismatch")
    );
}
