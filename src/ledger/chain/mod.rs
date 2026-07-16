mod backfill;
mod verify;

use rusqlite::{Connection, OptionalExtension, params};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::LegitimacyError;

pub(super) const COMPILED_RULES_TABLE: &str = "compiled_rules";
pub(super) const CERTIFICATES_TABLE: &str = "certificates";
pub(super) const DECLARED_SACRIFICES_TABLE: &str = "declared_sacrifices";
pub(super) const PARADOX_RESULTS_TABLE: &str = "paradox_results";
const CHAIN_HEADS_TABLE: &str = "ledger_chain_heads";

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ChainVerificationResult {
    pub valid: bool,
    pub tables: Vec<TableChainStatus>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct TableChainStatus {
    pub table: String,
    pub valid: bool,
    pub checked_rows: usize,
    pub error: Option<String>,
}

pub(super) fn verify_chain(
    connection: &Connection,
) -> Result<ChainVerificationResult, LegitimacyError> {
    // Wrap verification in a deferred (read-only) transaction so every
    // sub-table scan and chain-head lookup observes a single consistent
    // SQLite snapshot. Without this, a concurrent writer in another
    // process can insert into a table and update ledger_chain_heads
    // between the scan-rows query and the chain-head query within the
    // same logical verification, producing a false-negative chain break
    // (anchored row_count ahead of observed row count).
    run_in_deferred_transaction(connection, "verifying ledger chain", |connection| {
        let tables = vec![
            verify::verify_compiled_rules_chain(connection)?,
            verify::verify_certificates_chain(connection)?,
            verify::verify_declared_sacrifices_chain(connection)?,
            verify::verify_paradox_results_chain(connection)?,
        ];
        let valid = tables.iter().all(|table| table.valid);
        Ok(ChainVerificationResult { valid, tables })
    })
}

pub(super) fn ensure_chain_schema(connection: &Connection) -> Result<(), LegitimacyError> {
    connection
        .execute(
            &format!(
                "CREATE TABLE IF NOT EXISTS {CHAIN_HEADS_TABLE} (
                table_name TEXT PRIMARY KEY,
                row_count INTEGER NOT NULL,
                head_hash TEXT NOT NULL
            )"
            ),
            [],
        )
        .map_err(|source| LegitimacyError::Sqlite {
            context: "creating ledger chain head schema".to_string(),
            source,
        })?;

    for table in [
        COMPILED_RULES_TABLE,
        CERTIFICATES_TABLE,
        DECLARED_SACRIFICES_TABLE,
        PARADOX_RESULTS_TABLE,
    ] {
        backfill::ensure_chain_columns(connection, table)?;
    }

    if backfill::table_needs_backfill(connection, COMPILED_RULES_TABLE)? {
        backfill::backfill_compiled_rules_chain(connection)?;
    }
    if backfill::table_needs_backfill(connection, CERTIFICATES_TABLE)? {
        backfill::backfill_certificates_chain(connection)?;
    }
    if backfill::table_needs_backfill(connection, DECLARED_SACRIFICES_TABLE)? {
        backfill::backfill_declared_sacrifices_chain(connection)?;
    }
    if backfill::table_needs_backfill(connection, PARADOX_RESULTS_TABLE)? {
        backfill::backfill_paradox_results_chain(connection)?;
    }

    for table in [
        COMPILED_RULES_TABLE,
        CERTIFICATES_TABLE,
        DECLARED_SACRIFICES_TABLE,
        PARADOX_RESULTS_TABLE,
    ] {
        initialize_chain_head(connection, table)?;
    }

    Ok(())
}

pub(super) fn previous_hash(
    connection: &Connection,
    table: &str,
) -> Result<String, LegitimacyError> {
    connection
        .query_row(
            &format!("SELECT row_hash FROM {table} ORDER BY rowid DESC LIMIT 1"),
            [],
            |row| row.get(0),
        )
        .or_else(|source| match source {
            rusqlite::Error::QueryReturnedNoRows => Ok(String::new()),
            other => Err(other),
        })
        .map_err(|source| LegitimacyError::Sqlite {
            context: format!("reading previous hash from '{table}'"),
            source,
        })
}

pub(super) fn insert_paradox_row(
    connection: &Connection,
    rule_name: &str,
    paradox_type: &str,
    description: &str,
    detected_at: &str,
) -> Result<(), LegitimacyError> {
    run_in_immediate_transaction(connection, "recording paradox result", |connection| {
        let prev_hash = previous_hash(connection, PARADOX_RESULTS_TABLE)?;
        let content_json =
            paradox_result_content_json(rule_name, paradox_type, description, detected_at);

        connection
            .execute(
                "INSERT INTO paradox_results
                 (rule_name, paradox_type, description, detected_at, prev_hash, row_hash)
                 VALUES (?1, ?2, ?3, ?4, ?5, '')",
                params![
                    rule_name,
                    paradox_type,
                    description,
                    detected_at,
                    prev_hash.as_str()
                ],
            )
            .map_err(|source| LegitimacyError::Sqlite {
                context: "recording paradox result".to_string(),
                source,
            })?;
        let rowid = connection.last_insert_rowid();
        let row_hash = chain_hash(prev_hash.as_str(), rowid, content_json.as_str());
        connection
            .execute(
                "UPDATE paradox_results SET row_hash = ?1 WHERE rowid = ?2",
                params![row_hash.as_str(), rowid],
            )
            .map_err(|source| LegitimacyError::Sqlite {
                context: "finalizing paradox hash".to_string(),
                source,
            })?;
        update_chain_head(connection, PARADOX_RESULTS_TABLE, row_hash.as_str())?;
        Ok(())
    })
}

pub(super) fn update_chain_head(
    connection: &Connection,
    table: &str,
    head_hash: &str,
) -> Result<(), LegitimacyError> {
    let row_count = table_row_count(connection, table)?;
    connection
        .execute(
            &format!(
                "INSERT INTO {CHAIN_HEADS_TABLE} (table_name, row_count, head_hash)
             VALUES (?1, ?2, ?3)
             ON CONFLICT(table_name) DO UPDATE SET
                row_count = excluded.row_count,
                head_hash = excluded.head_hash"
            ),
            params![table, row_count, head_hash],
        )
        .map_err(|source| LegitimacyError::Sqlite {
            context: format!("updating chain head for '{table}'"),
            source,
        })?;
    Ok(())
}

pub(super) fn verify_chain_head(
    connection: &Connection,
    table: &str,
    checked_rows: usize,
    observed_head_hash: &str,
) -> Result<Option<TableChainStatus>, LegitimacyError> {
    let expected = connection
        .query_row(
            &format!("SELECT row_count, head_hash FROM {CHAIN_HEADS_TABLE} WHERE table_name = ?1"),
            params![table],
            |row| Ok((row.get::<_, i64>(0)?, row.get::<_, String>(1)?)),
        )
        .optional()
        .map_err(|source| LegitimacyError::Sqlite {
            context: format!("reading chain head for '{table}'"),
            source,
        })?;

    let Some((expected_rows, expected_hash)) = expected else {
        return Ok(Some(invalid_table_status(
            table,
            checked_rows,
            "missing anchored chain head".to_string(),
        )));
    };

    if expected_rows != checked_rows as i64 {
        return Ok(Some(invalid_table_status(
            table,
            checked_rows,
            format!("anchored row_count {expected_rows} does not match observed {checked_rows}"),
        )));
    }

    if expected_hash != observed_head_hash {
        return Ok(Some(invalid_table_status(
            table,
            checked_rows,
            "anchored head_hash does not match observed head".to_string(),
        )));
    }

    Ok(None)
}

fn initialize_chain_head(connection: &Connection, table: &str) -> Result<(), LegitimacyError> {
    let existing: Option<i64> = connection
        .query_row(
            &format!("SELECT row_count FROM {CHAIN_HEADS_TABLE} WHERE table_name = ?1"),
            params![table],
            |row| row.get(0),
        )
        .optional()
        .map_err(|source| LegitimacyError::Sqlite {
            context: format!("checking chain head for '{table}'"),
            source,
        })?;
    if existing.is_some() {
        return Ok(());
    }

    let head_hash = previous_hash(connection, table)?;
    update_chain_head(connection, table, head_hash.as_str())
}

fn table_row_count(connection: &Connection, table: &str) -> Result<i64, LegitimacyError> {
    connection
        .query_row(&format!("SELECT COUNT(*) FROM {table}"), [], |row| {
            row.get(0)
        })
        .map_err(|source| LegitimacyError::Sqlite {
            context: format!("counting rows in '{table}'"),
            source,
        })
}

pub(super) fn compiled_rule_content_json(
    name: &str,
    version: &str,
    admissible: bool,
    family_description: &str,
    compiled_at: &str,
    axiom_verdicts_json: &str,
    strategyproofness_json: &str,
) -> String {
    serde_json::json!({
        "name": name,
        "version": version,
        "admissible": admissible,
        "family_description": family_description,
        "compiled_at": compiled_at,
        "axiom_verdicts_json": axiom_verdicts_json,
        "strategyproofness_json": strategyproofness_json
    })
    .to_string()
}

pub(super) fn legacy_compiled_rule_content_json(
    name: &str,
    version: &str,
    admissible: bool,
    family_description: &str,
    compiled_at: &str,
    axiom_verdicts_json: &str,
) -> String {
    serde_json::json!({
        "name": name,
        "version": version,
        "admissible": admissible,
        "family_description": family_description,
        "compiled_at": compiled_at,
        "axiom_verdicts_json": axiom_verdicts_json
    })
    .to_string()
}

pub(super) fn certificate_content_json(
    rule_name: &str,
    rule_version: &str,
    compiled_rule_hash: &str,
    claimant_id: &str,
    outcome: f64,
    evidence_json: &str,
    issued_at: &str,
) -> String {
    serde_json::json!({
        "rule_name": rule_name,
        "rule_version": rule_version,
        "compiled_rule_hash": compiled_rule_hash,
        "claimant_id": claimant_id,
        "outcome": outcome,
        "evidence_json": evidence_json,
        "issued_at": issued_at
    })
    .to_string()
}

pub(super) fn legacy_certificate_content_json(
    rule_name: &str,
    rule_version: &str,
    claimant_id: &str,
    outcome: f64,
    evidence_json: &str,
    issued_at: &str,
) -> String {
    serde_json::json!({
        "rule_name": rule_name,
        "rule_version": rule_version,
        "claimant_id": claimant_id,
        "outcome": outcome,
        "evidence_json": evidence_json,
        "issued_at": issued_at
    })
    .to_string()
}

pub(super) struct DeclaredSacrificeChainContent<'a> {
    pub compiled_kind: &'a str,
    pub subject_name: &'a str,
    pub subject_version: &'a str,
    pub sacrificed_property: &'a str,
    pub justification: &'a str,
    pub impact_bound: f64,
    pub monitoring_plan_json: &'a str,
    pub provenance_json: &'a str,
    pub declared_at: &'a str,
}

pub(super) fn declared_sacrifice_content_json(
    content: &DeclaredSacrificeChainContent<'_>,
) -> String {
    serde_json::json!({
        "compiled_kind": content.compiled_kind,
        "subject_name": content.subject_name,
        "subject_version": content.subject_version,
        "sacrificed_property": content.sacrificed_property,
        "justification": content.justification,
        "impact_bound": content.impact_bound,
        "monitoring_plan_json": content.monitoring_plan_json,
        "provenance_json": content.provenance_json,
        "declared_at": content.declared_at
    })
    .to_string()
}

pub(super) fn paradox_result_content_json(
    rule_name: &str,
    paradox_type: &str,
    description: &str,
    detected_at: &str,
) -> String {
    serde_json::json!({
        "rule_name": rule_name,
        "paradox_type": paradox_type,
        "description": description,
        "detected_at": detected_at
    })
    .to_string()
}

pub(super) fn chain_hash(prev_hash: &str, rowid: i64, content_json: &str) -> String {
    let mut hasher = Sha256::new();
    hasher.update(prev_hash.as_bytes());
    hasher.update(rowid.to_string().as_bytes());
    hasher.update(content_json.as_bytes());
    let digest = hasher.finalize();
    let mut encoded = String::with_capacity(digest.len() * 2);
    for byte in digest {
        use std::fmt::Write as _;
        let _ = write!(&mut encoded, "{byte:02x}");
    }
    encoded
}

pub(super) fn run_in_deferred_transaction<T>(
    connection: &Connection,
    context: &str,
    f: impl FnOnce(&Connection) -> Result<T, LegitimacyError>,
) -> Result<T, LegitimacyError> {
    // Deferred transactions establish a SQLite snapshot at the first read
    // and hold it until COMMIT/ROLLBACK. Use this for read-only flows that
    // must observe a single consistent view across multiple statements
    // (e.g., chain verification across tables and chain-head anchors).
    connection
        .execute_batch("BEGIN DEFERRED TRANSACTION")
        .map_err(|source| LegitimacyError::Sqlite {
            context: format!("starting {context} transaction"),
            source,
        })?;

    let result = f(connection);
    match result {
        Ok(value) => {
            connection
                .execute_batch("COMMIT")
                .map_err(|source| LegitimacyError::Sqlite {
                    context: format!("committing {context} transaction"),
                    source,
                })?;
            Ok(value)
        }
        Err(error) => {
            let _ = connection.execute_batch("ROLLBACK");
            Err(error)
        }
    }
}

pub(super) fn run_in_immediate_transaction<T>(
    connection: &Connection,
    context: &str,
    f: impl FnOnce(&Connection) -> Result<T, LegitimacyError>,
) -> Result<T, LegitimacyError> {
    connection
        .execute_batch("BEGIN IMMEDIATE TRANSACTION")
        .map_err(|source| LegitimacyError::Sqlite {
            context: format!("starting {context} transaction"),
            source,
        })?;

    let result = f(connection);
    match result {
        Ok(value) => {
            connection
                .execute_batch("COMMIT")
                .map_err(|source| LegitimacyError::Sqlite {
                    context: format!("committing {context} transaction"),
                    source,
                })?;
            Ok(value)
        }
        Err(error) => {
            let _ = connection.execute_batch("ROLLBACK");
            Err(error)
        }
    }
}

pub(super) fn valid_table_status(table: &str, checked_rows: usize) -> TableChainStatus {
    TableChainStatus {
        table: table.to_string(),
        valid: true,
        checked_rows,
        error: None,
    }
}

pub(super) fn invalid_table_status(
    table: &str,
    checked_rows: usize,
    error: String,
) -> TableChainStatus {
    TableChainStatus {
        table: table.to_string(),
        valid: false,
        checked_rows,
        error: Some(error),
    }
}
