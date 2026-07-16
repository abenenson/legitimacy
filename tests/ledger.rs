use std::{
    collections::BTreeMap,
    fs,
    path::PathBuf,
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

use legitimacy::{
    Allocation, Certificate, Claim, Claimant, CompiledRule, Estate, PositiveStrength, Rule,
    RuleSpec, ValidAllocation, Verdict,
    certificate::{CertificationContext, certify},
    compiler::{Family, compile},
    ledger::{Ledger, LedgerQuery},
    paradox::{ParadoxType, ParadoxViolation, run_paradox_suite},
    rules::claude_agent_sdk_permissions_rule,
};
use rusqlite::Connection;
use serial_test::serial;

fn claimant_with_class(id: &str, priority_class: &str) -> Claimant {
    Claimant {
        id: id.to_string(),
        priority_class: priority_class.to_string(),
        attributes: BTreeMap::new(),
    }
}

fn family() -> Family {
    Family {
        reductions: true,
        shocks: vec![0.5, 1.5],
        strengthening_deltas: vec![
            PositiveStrength::new(0.1).unwrap(),
            PositiveStrength::new(0.5).unwrap(),
        ],
        monotonicity_inversion: false,
    }
}

fn permission_claim(id: &str, base_authorization: f64) -> Claim {
    Claim::new(id, 1.0)
        .unwrap()
        .with_metric("available", 1.0)
        .with_metric("listed", 1.0)
        .with_metric(
            "denied",
            if base_authorization <= f64::EPSILON {
                1.0
            } else {
                0.0
            },
        )
        .with_metric("base_authorization", base_authorization)
}

fn permissions_runtime(
    rule_name: &str,
    rule_version: &str,
) -> (Rule, Vec<Claim>, Vec<Claimant>, Estate) {
    let mut rule = claude_agent_sdk_permissions_rule();
    rule.name = rule_name.to_string();
    rule.version = rule_version.to_string();
    let claims = vec![
        permission_claim("Read", 1.0),
        permission_claim("Bash", 0.5),
        permission_claim("WebFetch", 0.0),
    ];
    let claimants = vec![
        claimant_with_class("Read", "always_allow"),
        claimant_with_class("Bash", "ask_user"),
        claimant_with_class("WebFetch", "always_deny"),
    ];
    let estate = Estate::new(1.0, "authorization").unwrap();
    (rule, claims, claimants, estate)
}

fn temp_ledger_path(label: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!("verdict-{label}-{nanos}.sqlite3"))
}

fn compiled_rule(name: &str, version: &str, compiled_at: &str) -> CompiledRule {
    CompiledRule {
        name: name.to_string(),
        version: version.to_string(),
        axiom_verdicts: vec![Verdict::Admissible {
            axiom: "consistency".to_string(),
            perturbations_tested: 1,
        }],
        strategyproofness: legitimacy::StrategyproofnessVerdict::Strategyproof,
        family_description: "test-family".to_string(),
        compiled_at: compiled_at.to_string(),
    }
}

fn certificate(
    rule_name: &str,
    rule_version: &str,
    claimant_id: &str,
    issued_at: &str,
) -> Certificate {
    Certificate {
        rule_name: rule_name.to_string(),
        rule_version: rule_version.to_string(),
        compiled_rule_hash: "test-compiled-rule-hash".to_string(),
        act_description: "test certificate".to_string(),
        claimant_id: claimant_id.to_string(),
        outcome: 1.0,
        evidence: BTreeMap::from([("source".to_string(), "test".to_string())]),
        issued_at: issued_at.to_string(),
        admissible: true,
    }
}

fn paradox_rule(name: &str, version: &str) -> Rule {
    Rule {
        name: name.to_string(),
        version: version.to_string(),
        rule_spec: RuleSpec::programmatic(|claims: &[Claim], _estate: &Estate| {
            Ok(claims
                .iter()
                .map(|claim| (claim.claimant_id.clone(), 1.0))
                .collect::<Allocation>())
        }),
        priority_classes: vec!["standard".to_string()],
    }
}

fn single_claim_allocation(claimant_id: &str, value: f64) -> ValidAllocation {
    ValidAllocation::new(
        Allocation::from(BTreeMap::from([(claimant_id.to_string(), value)])),
        &[Claim::new(claimant_id, 1.0).unwrap()],
    )
    .unwrap()
}

#[test]
#[serial]
fn compile_writes_to_ledger() {
    let rule_name = "ledger-compile";
    let rule_version = "compile-1";
    let (rule, claims, claimants, estate) = permissions_runtime(rule_name, rule_version);

    let compiled = compile(&rule, &claims, &estate, &claimants, &family()).unwrap();
    assert!(compiled.is_admissible());

    let ledger = Ledger::open_default().unwrap();
    let report = ledger
        .audit(&LedgerQuery {
            rule_name: Some(rule_name.to_string()),
            rule_version: Some(rule_version.to_string()),
            claimant_id: None,
            limit: 10,
        })
        .unwrap();

    assert!(
        report
            .compiled_rules
            .iter()
            .any(|record| record.name == rule_name && record.version == rule_version)
    );
}

#[test]
#[serial]
fn certify_writes_to_ledger() {
    let rule_name = "ledger-certify";
    let rule_version = "certify-1";
    let (rule, claims, claimants, estate) = permissions_runtime(rule_name, rule_version);

    let compiled = compile(&rule, &claims, &estate, &claimants, &family()).unwrap();
    let mut evidence = BTreeMap::new();
    evidence.insert("source".to_string(), "ledger-test".to_string());
    let certificate = certify(
        &CertificationContext {
            compiled_rule: &compiled,
            rule: &rule,
            claims: &claims,
            estate: &estate,
        },
        "Test certificate",
        "Read",
        1.0,
        evidence.clone(),
    )
    .unwrap();

    let ledger = Ledger::open_default().unwrap();
    let report = ledger
        .audit(&LedgerQuery {
            rule_name: Some(rule_name.to_string()),
            rule_version: Some(rule_version.to_string()),
            claimant_id: Some("Read".to_string()),
            limit: 10,
        })
        .unwrap();

    assert!(report.certificates.iter().any(|record| {
        record.rule_name == rule_name
            && record.rule_version == rule_version
            && record.compiled_rule_hash == certificate.compiled_rule_hash
            && record.claimant_id == "Read"
            && (record.outcome - certificate.outcome).abs() < 1e-9
            && record.evidence == evidence
    }));
}

#[test]
#[serial]
fn ledger_is_queryable_across_all_tables() {
    let rule_name = "ledger-audit";
    let rule_version = "audit-1";
    let (rule, claims, claimants, estate) = permissions_runtime(rule_name, rule_version);

    let compiled = compile(&rule, &claims, &estate, &claimants, &family()).unwrap();
    let _certificate = certify(
        &CertificationContext {
            compiled_rule: &compiled,
            rule: &rule,
            claims: &claims,
            estate: &estate,
        },
        "Audit lookup certificate",
        "Read",
        1.0,
        BTreeMap::from([("source".to_string(), "query".to_string())]),
    )
    .unwrap();
    let _violations = run_paradox_suite(&rule, &claims, &estate, &claimants).unwrap();

    let ledger = Ledger::open_default().unwrap();
    let report = ledger
        .audit(&LedgerQuery {
            rule_name: Some(rule_name.to_string()),
            rule_version: Some(rule_version.to_string()),
            claimant_id: Some("Read".to_string()),
            limit: 10,
        })
        .unwrap();

    assert!(!report.compiled_rules.is_empty());
    assert!(!report.certificates.is_empty());
    assert!(!report.paradox_results.is_empty());
    assert!(
        report
            .paradox_results
            .iter()
            .all(|record| record.rule_name == rule_name)
    );
}

#[test]
#[serial]
fn ledger_audit_round_trips_compiled_rule_strategyproofness() {
    let path = temp_ledger_path("strategyproofness-roundtrip");
    let ledger = Ledger::open(&path).unwrap();
    let mut compiled = compiled_rule("strategy-audit", "1", "2026-04-14T00:00:01Z");
    compiled.strategyproofness = legitimacy::StrategyproofnessVerdict::Manipulable {
        claimant: "alice".to_string(),
        true_strength: 1.0,
        reported: 2.0,
        true_alloc: 0.4,
        manipulated_alloc: 0.7,
    };

    ledger.record_compiled_rule(&compiled).unwrap();

    let report = ledger
        .audit(&LedgerQuery {
            rule_name: Some("strategy-audit".to_string()),
            rule_version: Some("1".to_string()),
            claimant_id: None,
            limit: 10,
        })
        .unwrap();

    assert_eq!(report.compiled_rules.len(), 1);
    assert_eq!(
        report.compiled_rules[0].strategyproofness,
        compiled.strategyproofness
    );

    let _ = fs::remove_file(path);
}

#[test]
#[serial]
fn ledger_hash_chain_detects_tampering() {
    let path = temp_ledger_path("chain");
    let ledger = Ledger::open(&path).unwrap();
    ledger
        .record_compiled_rule(&compiled_rule("alpha", "1", "2026-04-14T00:00:01Z"))
        .unwrap();
    ledger
        .record_compiled_rule(&compiled_rule("beta", "1", "2026-04-14T00:00:02Z"))
        .unwrap();
    ledger
        .record_certificate(&certificate("alpha", "1", "alice", "2026-04-14T00:00:03Z"))
        .unwrap();
    ledger
        .record_certificate(&certificate("beta", "1", "bob", "2026-04-14T00:00:04Z"))
        .unwrap();
    ledger
        .record_paradox_results(
            &paradox_rule("alpha", "1"),
            &[ParadoxViolation {
                paradox_type: ParadoxType::Population,
                description: "tamper test".to_string(),
                original_allocation: single_claim_allocation("alice", 1.0),
                perturbed_allocation: single_claim_allocation("alice", 0.0),
            }],
        )
        .unwrap();

    let valid = ledger.verify_chain().unwrap();
    assert!(valid.valid);

    let connection = Connection::open(&path).unwrap();
    connection
        .execute(
            "UPDATE certificates SET claimant_id = 'mallory' WHERE rowid = 2",
            [],
        )
        .unwrap();

    let invalid = ledger.verify_chain().unwrap();
    assert!(!invalid.valid);
    assert!(
        invalid
            .tables
            .iter()
            .any(|table| table.table == "certificates" && !table.valid)
    );

    let _ = fs::remove_file(path);
}

#[test]
#[serial]
fn ledger_hash_chain_detects_strategyproofness_tampering() {
    let path = temp_ledger_path("strategyproofness-tamper");
    let ledger = Ledger::open(&path).unwrap();
    ledger
        .record_compiled_rule(&compiled_rule("alpha", "1", "2026-04-14T00:00:01Z"))
        .unwrap();

    assert!(ledger.verify_chain().unwrap().valid);

    let tampered_strategyproofness =
        serde_json::to_string(&legitimacy::StrategyproofnessVerdict::Manipulable {
            claimant: "mallory".to_string(),
            true_strength: 1.0,
            reported: 2.0,
            true_alloc: 0.0,
            manipulated_alloc: 1.0,
        })
        .unwrap();
    let connection = Connection::open(&path).unwrap();
    connection
        .execute(
            "UPDATE compiled_rules SET strategyproofness_json = ?1 WHERE rowid = 1",
            [tampered_strategyproofness.as_str()],
        )
        .unwrap();

    let invalid = ledger.verify_chain().unwrap();
    assert!(!invalid.valid);
    assert!(
        invalid
            .tables
            .iter()
            .any(|table| table.table == "compiled_rules" && !table.valid)
    );

    let _ = fs::remove_file(path);
}

#[test]
#[serial]
fn ledger_hash_chain_detects_tail_deletion() {
    let path = temp_ledger_path("tail-delete");
    let ledger = Ledger::open(&path).unwrap();
    ledger
        .record_compiled_rule(&compiled_rule("alpha", "1", "2026-04-14T00:00:01Z"))
        .unwrap();
    ledger
        .record_compiled_rule(&compiled_rule("beta", "1", "2026-04-14T00:00:02Z"))
        .unwrap();

    assert!(ledger.verify_chain().unwrap().valid);

    let connection = Connection::open(&path).unwrap();
    connection
        .execute("DELETE FROM compiled_rules WHERE rowid = 2", [])
        .unwrap();

    let invalid = ledger.verify_chain().unwrap();
    assert!(!invalid.valid);
    assert!(invalid.tables.iter().any(|table| {
        table.table == "compiled_rules"
            && !table.valid
            && table
                .error
                .as_deref()
                .is_some_and(|error| error.contains("row_count"))
    }));

    let _ = fs::remove_file(path);
}

#[test]
#[serial]
fn audit_verify_chain_cli_reports_breaks() {
    let path = temp_ledger_path("chain-cli");
    let ledger = Ledger::open(&path).unwrap();
    for (index, name) in ["alpha", "beta", "gamma", "delta", "epsilon"]
        .into_iter()
        .enumerate()
    {
        ledger
            .record_compiled_rule(&compiled_rule(
                name,
                "1",
                &format!("2026-04-14T00:00:0{}Z", index + 1),
            ))
            .unwrap();
    }

    let ok = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .args([
            "audit",
            "--ledger",
            path.to_str().unwrap(),
            "--verify-chain",
        ])
        .output()
        .unwrap();
    assert!(ok.status.success());
    let ok_stdout = String::from_utf8(ok.stdout).unwrap();
    assert!(ok_stdout.contains("\"valid\": true"));

    let connection = Connection::open(&path).unwrap();
    connection
        .execute(
            "UPDATE compiled_rules SET family_description = 'tampered' WHERE rowid = 3",
            [],
        )
        .unwrap();

    let broken = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .args([
            "audit",
            "--ledger",
            path.to_str().unwrap(),
            "--verify-chain",
        ])
        .output()
        .unwrap();
    assert!(!broken.status.success());
    let broken_stdout = String::from_utf8(broken.stdout).unwrap();
    assert!(broken_stdout.contains("\"valid\": false"));

    let _ = fs::remove_file(path);
}

#[test]
#[serial]
fn verify_chain_runs_under_a_consistent_snapshot() {
    // Regression test for the verify_chain false-negative race observed in
    // tests/sacrifice.rs::compile_with_sacrifices_and_monitor_writes_sacrifices_to_hash_chain_ledger
    // when concurrent cargo test processes share .legitimacy/ledger.sqlite3.
    //
    // Mechanism of the original bug: verify_chain ran each table scan and
    // each chain-head lookup as separate auto-commit reads. In SQLite WAL
    // mode, each auto-commit read picks a fresh snapshot. A concurrent
    // writer's atomic transaction (which inserts a row + bumps the
    // ledger_chain_heads anchor in lockstep) could commit between the
    // verifier's table-rows scan and chain-head lookup, exposing one part
    // of the writer's transaction to the verifier and not the other —
    // surfacing as 'anchored row_count N+1 does not match observed N'.
    //
    // Fix: verify_chain wraps all reads in a BEGIN DEFERRED transaction
    // so every sub-table scan and chain-head lookup share one snapshot.
    //
    // This test exercises the property by running a writer thread on a
    // separate SQLite connection that mirrors the production write path:
    // inside one transaction, INSERT into paradox_results and bump
    // ledger_chain_heads.row_count. The verifier loops verify_chain on a
    // separate connection. Without the snapshot, a fraction of verifier
    // calls observe the writer's chain-head bump but not the writer's
    // table insert (or vice versa) and report a row_count mismatch.
    use rusqlite::{Connection, params};
    use std::sync::Arc;
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    use std::thread;
    use std::time::Duration;

    let path = temp_ledger_path("verify-snapshot");
    let ledger = Ledger::open(&path).unwrap();
    ledger
        .record_compiled_rule(&compiled_rule(
            "snapshot-rule",
            "v1",
            "2026-04-29T00:00:00Z",
        ))
        .unwrap();
    ledger
        .record_paradox_results(&paradox_rule("snapshot-paradox", "v1"), &[])
        .unwrap();

    let baseline = ledger.verify_chain().unwrap();
    assert!(baseline.valid);

    let stop = Arc::new(AtomicBool::new(false));
    let row_count_mismatches = Arc::new(AtomicUsize::new(0));
    let writer_path = path.clone();
    let writer_stop = stop.clone();
    let writer = thread::spawn(move || {
        let conn = Connection::open(&writer_path).unwrap();
        conn.busy_timeout(Duration::from_secs(5)).unwrap();
        let mut counter: u64 = 0;
        while !writer_stop.load(Ordering::Relaxed) {
            counter += 1;
            // Mirror the production write path: insert a paradox_results
            // row and bump ledger_chain_heads atomically in one
            // transaction. The hashes are intentionally empty here — the
            // verifier MAY flag a content-hash mismatch on the writer's
            // rows, but it must NOT flag a row_count mismatch, because
            // the writer's INSERT and chain-head bump are atomic.
            conn.execute_batch("BEGIN IMMEDIATE TRANSACTION").unwrap();
            // Use a non-empty placeholder row_hash so the verifier-side
            // ensure_chain_schema does not trigger a backfill (which races
            // with the writer for the SQLite write lock).
            conn.execute(
                "INSERT INTO paradox_results
                 (rule_name, paradox_type, description, detected_at, prev_hash, row_hash)
                 VALUES (?1, 'none', 'concurrent-writer', '2026-04-29T00:00:00Z', 'xx', 'xx')",
                params![format!("writer-{counter}")],
            )
            .unwrap();
            let row_count: i64 = conn
                .query_row("SELECT COUNT(*) FROM paradox_results", [], |r| r.get(0))
                .unwrap();
            conn.execute(
                "INSERT INTO ledger_chain_heads (table_name, row_count, head_hash)
                 VALUES ('paradox_results', ?1, '')
                 ON CONFLICT(table_name) DO UPDATE SET
                    row_count = excluded.row_count,
                    head_hash = excluded.head_hash",
                params![row_count],
            )
            .unwrap();
            conn.execute_batch("COMMIT").unwrap();
            thread::sleep(Duration::from_micros(20));
        }
    });

    let verifier_path = path.clone();
    let mismatch_counter = row_count_mismatches.clone();
    let verifier = thread::spawn(move || {
        let verifier_ledger = Ledger::open(&verifier_path).unwrap();
        for _ in 0..400 {
            let result = verifier_ledger.verify_chain().unwrap();
            for table in &result.tables {
                if let Some(error) = table.error.as_deref()
                    && error.contains("row_count")
                {
                    mismatch_counter.fetch_add(1, Ordering::Relaxed);
                }
            }
        }
    });

    verifier.join().unwrap();
    stop.store(true, Ordering::Relaxed);
    writer.join().unwrap();

    assert_eq!(
        row_count_mismatches.load(Ordering::Relaxed),
        0,
        "verify_chain reported row_count snapshot mismatches under          concurrent writes — verify_chain is not snapshot-pinned"
    );

    let _ = fs::remove_file(path);
}

#[test]
#[serial]
fn audit_runs_under_a_consistent_snapshot() {
    // Regression test for the audit() snapshot inconsistency identified in
    // runs/pre-tag-comprehensive-audit-2026-04-29.md. Same root cause as
    // verify_chain_runs_under_a_consistent_snapshot above:
    //
    // Ledger::audit() runs four cross-table SELECTs (compiled_rules,
    // certificates, declared_sacrifices, paradox_results). In SQLite WAL
    // mode without an enclosing transaction, each SELECT picks a fresh
    // snapshot. A concurrent cross-process writer that atomically
    // commits matched rows across two of those tables can interleave
    // between two of the auditor's reads, exposing the writer's
    // contribution to one table but not the other and producing a torn
    // audit report.
    //
    // Fix: audit() wraps the four reads in a BEGIN DEFERRED transaction
    // (chain::run_in_deferred_transaction). All four loads observe one
    // pinned snapshot.
    //
    // The test uses a separate rusqlite::Connection (bypassing the
    // in-process LEDGER_LOCK so we genuinely simulate a second process)
    // to atomically INSERT a matched pair: one row in compiled_rules
    // and one row in paradox_results sharing a writer key. The auditor
    // loops audit() calls and counts how many reports show a torn
    // cross-table count (compiled_rules count != paradox_results count
    // for the writer's key prefix). Without the fix this is non-zero.
    use rusqlite::{Connection, params};
    use std::sync::Arc;
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    use std::thread;
    use std::time::Duration;

    let path = temp_ledger_path("audit-snapshot");
    let ledger = Ledger::open(&path).unwrap();
    // Seed the ledger so all schema/chain tables exist before either
    // thread opens its connection. Avoids ensure_chain_schema racing
    // the writer for the SQLite write lock on first use.
    ledger
        .record_compiled_rule(&compiled_rule(
            "audit-snapshot-seed",
            "v1",
            "2026-04-29T00:00:00Z",
        ))
        .unwrap();
    ledger
        .record_paradox_results(&paradox_rule("audit-snapshot-seed", "v1"), &[])
        .unwrap();

    let stop = Arc::new(AtomicBool::new(false));
    let torn_reports = Arc::new(AtomicUsize::new(0));
    let writer_path = path.clone();
    let writer_stop = stop.clone();
    let writer = thread::spawn(move || {
        let conn = Connection::open(&writer_path).unwrap();
        conn.busy_timeout(Duration::from_secs(5)).unwrap();
        let mut counter: u64 = 0;
        while !writer_stop.load(Ordering::Relaxed) {
            counter += 1;
            let key = format!("audit-writer-{counter}");
            // Atomic two-table insert: compiled_rules + paradox_results
            // commit together. If audit() observes a snapshot taken
            // between these two table inserts (or after the COMMIT for
            // one read but before the COMMIT for another),
            // cross-table counts will diverge.
            //
            // Hashes are non-empty placeholders so verifier-side
            // ensure_chain_schema does not trigger a backfill that
            // races the writer for the SQLite write lock. We do NOT
            // update ledger_chain_heads here — that would invalidate
            // the chain anchor and is unrelated to the audit() race
            // we are exercising.
            conn.execute_batch("BEGIN IMMEDIATE TRANSACTION").unwrap();
            conn.execute(
                "INSERT INTO compiled_rules
                 (name, version, admissible, family_description, compiled_at,
                  axiom_verdicts_json, strategyproofness_json, prev_hash, row_hash)
                 VALUES (?1, 'v1', 1, 'writer', '2026-04-29T00:00:00Z',
                         '[]', '\"Strategyproof\"', 'xx', 'xx')",
                params![key],
            )
            .unwrap();
            conn.execute(
                "INSERT INTO paradox_results
                 (rule_name, paradox_type, description, detected_at, prev_hash, row_hash)
                 VALUES (?1, 'none', 'paired', '2026-04-29T00:00:00Z', 'xx', 'xx')",
                params![key],
            )
            .unwrap();
            conn.execute_batch("COMMIT").unwrap();
            thread::sleep(Duration::from_micros(20));
        }
    });

    let auditor_path = path.clone();
    let torn_counter = torn_reports.clone();
    let auditor = thread::spawn(move || {
        let auditor_ledger = Ledger::open(&auditor_path).unwrap();
        for _ in 0..400 {
            // Limit large enough to capture every writer row produced
            // during the test window; writer sleeps 20us between
            // commits so 400 iterations gives < a few thousand rows.
            let report = auditor_ledger
                .audit(&LedgerQuery {
                    rule_name: None,
                    rule_version: None,
                    claimant_id: None,
                    limit: 1_000_000,
                })
                .unwrap();
            let compiled_writer_count = report
                .compiled_rules
                .iter()
                .filter(|r| r.name.starts_with("audit-writer-"))
                .count();
            let paradox_writer_count = report
                .paradox_results
                .iter()
                .filter(|r| r.rule_name.starts_with("audit-writer-"))
                .count();
            if compiled_writer_count != paradox_writer_count {
                torn_counter.fetch_add(1, Ordering::Relaxed);
            }
        }
    });

    auditor.join().unwrap();
    stop.store(true, Ordering::Relaxed);
    writer.join().unwrap();

    assert_eq!(
        torn_reports.load(Ordering::Relaxed),
        0,
        "audit() returned reports with torn cross-table counts under concurrent writes — audit() is not snapshot-pinned"
    );

    let _ = fs::remove_file(path);
}
