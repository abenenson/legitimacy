use rusqlite::{Connection, params};

use crate::LegitimacyError;

use super::{
    DeclaredSacrificeChainContent, certificate_content_json, chain_hash,
    compiled_rule_content_json, declared_sacrifice_content_json, paradox_result_content_json,
};

pub(super) fn ensure_chain_columns(
    connection: &Connection,
    table: &str,
) -> Result<(), LegitimacyError> {
    let columns = table_columns(connection, table)?;
    if !columns.iter().any(|column| column == "prev_hash") {
        connection
            .execute(
                &format!("ALTER TABLE {table} ADD COLUMN prev_hash TEXT NOT NULL DEFAULT ''"),
                [],
            )
            .map_err(|source| LegitimacyError::Sqlite {
                context: format!("adding prev_hash column to '{table}'"),
                source,
            })?;
    }
    if !columns.iter().any(|column| column == "row_hash") {
        connection
            .execute(
                &format!("ALTER TABLE {table} ADD COLUMN row_hash TEXT NOT NULL DEFAULT ''"),
                [],
            )
            .map_err(|source| LegitimacyError::Sqlite {
                context: format!("adding row_hash column to '{table}'"),
                source,
            })?;
    }

    Ok(())
}

fn table_columns(connection: &Connection, table: &str) -> Result<Vec<String>, LegitimacyError> {
    let mut statement = connection
        .prepare(&format!("PRAGMA table_info({table})"))
        .map_err(|source| LegitimacyError::Sqlite {
            context: format!("reading schema for '{table}'"),
            source,
        })?;
    let rows = statement
        .query_map([], |row| row.get::<_, String>(1))
        .map_err(|source| LegitimacyError::Sqlite {
            context: format!("querying schema rows for '{table}'"),
            source,
        })?;

    let mut columns = Vec::new();
    for row in rows {
        columns.push(row.map_err(|source| LegitimacyError::Sqlite {
            context: format!("reading schema row for '{table}'"),
            source,
        })?);
    }

    Ok(columns)
}

pub(super) fn table_needs_backfill(
    connection: &Connection,
    table: &str,
) -> Result<bool, LegitimacyError> {
    let count: i64 = connection
        .query_row(
            &format!("SELECT COUNT(*) FROM {table} WHERE row_hash = ''"),
            [],
            |row| row.get(0),
        )
        .map_err(|source| LegitimacyError::Sqlite {
            context: format!("checking chain completeness for '{table}'"),
            source,
        })?;

    Ok(count > 0)
}

pub(super) fn backfill_compiled_rules_chain(
    connection: &Connection,
) -> Result<(), LegitimacyError> {
    let mut statement = connection
        .prepare(
            "SELECT rowid, name, version, admissible, family_description, compiled_at, axiom_verdicts_json, strategyproofness_json
             FROM compiled_rules
             ORDER BY rowid ASC",
        )
        .map_err(|source| LegitimacyError::Sqlite {
            context: "preparing compiled rule chain backfill".to_string(),
            source,
        })?;
    let rows = statement
        .query_map([], |row| {
            Ok((
                row.get::<_, i64>(0)?,
                row.get::<_, String>(1)?,
                row.get::<_, String>(2)?,
                row.get::<_, bool>(3)?,
                row.get::<_, String>(4)?,
                row.get::<_, String>(5)?,
                row.get::<_, String>(6)?,
                row.get::<_, String>(7)?,
            ))
        })
        .map_err(|source| LegitimacyError::Sqlite {
            context: "running compiled rule chain backfill".to_string(),
            source,
        })?;

    let mut previous = String::new();
    for row in rows {
        let (
            rowid,
            name,
            version,
            admissible,
            family_description,
            compiled_at,
            axiom_verdicts_json,
            strategyproofness_json,
        ) = row.map_err(|source| LegitimacyError::Sqlite {
            context: "reading compiled rule chain backfill row".to_string(),
            source,
        })?;
        let row_hash = chain_hash(
            previous.as_str(),
            rowid,
            compiled_rule_content_json(
                name.as_str(),
                version.as_str(),
                admissible,
                family_description.as_str(),
                compiled_at.as_str(),
                axiom_verdicts_json.as_str(),
                strategyproofness_json.as_str(),
            )
            .as_str(),
        );
        connection
            .execute(
                "UPDATE compiled_rules SET prev_hash = ?1, row_hash = ?2 WHERE rowid = ?3",
                params![previous.as_str(), row_hash.as_str(), rowid],
            )
            .map_err(|source| LegitimacyError::Sqlite {
                context: "updating compiled rule chain backfill".to_string(),
                source,
            })?;
        previous = row_hash;
    }

    Ok(())
}

pub(super) fn backfill_certificates_chain(connection: &Connection) -> Result<(), LegitimacyError> {
    let mut statement = connection
        .prepare(
            "SELECT rowid, rule_name, rule_version, compiled_rule_hash, claimant_id, outcome, evidence_json, issued_at
             FROM certificates
             ORDER BY rowid ASC",
        )
        .map_err(|source| LegitimacyError::Sqlite {
            context: "preparing certificate chain backfill".to_string(),
            source,
        })?;
    let rows = statement
        .query_map([], |row| {
            Ok((
                row.get::<_, i64>(0)?,
                row.get::<_, String>(1)?,
                row.get::<_, String>(2)?,
                row.get::<_, String>(3)?,
                row.get::<_, String>(4)?,
                row.get::<_, f64>(5)?,
                row.get::<_, String>(6)?,
                row.get::<_, String>(7)?,
            ))
        })
        .map_err(|source| LegitimacyError::Sqlite {
            context: "running certificate chain backfill".to_string(),
            source,
        })?;

    let mut previous = String::new();
    for row in rows {
        let (
            rowid,
            rule_name,
            rule_version,
            compiled_rule_hash,
            claimant_id,
            outcome,
            evidence_json,
            issued_at,
        ) = row.map_err(|source| LegitimacyError::Sqlite {
            context: "reading certificate chain backfill row".to_string(),
            source,
        })?;
        let row_hash = chain_hash(
            previous.as_str(),
            rowid,
            certificate_content_json(
                rule_name.as_str(),
                rule_version.as_str(),
                compiled_rule_hash.as_str(),
                claimant_id.as_str(),
                outcome,
                evidence_json.as_str(),
                issued_at.as_str(),
            )
            .as_str(),
        );
        connection
            .execute(
                "UPDATE certificates SET prev_hash = ?1, row_hash = ?2 WHERE rowid = ?3",
                params![previous.as_str(), row_hash.as_str(), rowid],
            )
            .map_err(|source| LegitimacyError::Sqlite {
                context: "updating certificate chain backfill".to_string(),
                source,
            })?;
        previous = row_hash;
    }

    Ok(())
}

pub(super) fn backfill_declared_sacrifices_chain(
    connection: &Connection,
) -> Result<(), LegitimacyError> {
    let mut statement = connection
        .prepare(
            "SELECT rowid, compiled_kind, subject_name, subject_version, sacrificed_property, justification, impact_bound, monitoring_plan_json, provenance_json, declared_at
             FROM declared_sacrifices
             ORDER BY rowid ASC",
        )
        .map_err(|source| LegitimacyError::Sqlite {
            context: "preparing declared sacrifice chain backfill".to_string(),
            source,
        })?;
    let rows = statement
        .query_map([], |row| {
            Ok((
                row.get::<_, i64>(0)?,
                row.get::<_, String>(1)?,
                row.get::<_, String>(2)?,
                row.get::<_, String>(3)?,
                row.get::<_, String>(4)?,
                row.get::<_, String>(5)?,
                row.get::<_, f64>(6)?,
                row.get::<_, String>(7)?,
                row.get::<_, String>(8)?,
                row.get::<_, String>(9)?,
            ))
        })
        .map_err(|source| LegitimacyError::Sqlite {
            context: "running declared sacrifice chain backfill".to_string(),
            source,
        })?;

    let mut previous = String::new();
    for row in rows {
        let (
            rowid,
            compiled_kind,
            subject_name,
            subject_version,
            sacrificed_property,
            justification,
            impact_bound,
            monitoring_plan_json,
            provenance_json,
            declared_at,
        ) = row.map_err(|source| LegitimacyError::Sqlite {
            context: "reading declared sacrifice chain backfill row".to_string(),
            source,
        })?;
        let row_hash = chain_hash(
            previous.as_str(),
            rowid,
            declared_sacrifice_content_json(&DeclaredSacrificeChainContent {
                compiled_kind: compiled_kind.as_str(),
                subject_name: subject_name.as_str(),
                subject_version: subject_version.as_str(),
                sacrificed_property: sacrificed_property.as_str(),
                justification: justification.as_str(),
                impact_bound,
                monitoring_plan_json: monitoring_plan_json.as_str(),
                provenance_json: provenance_json.as_str(),
                declared_at: declared_at.as_str(),
            })
            .as_str(),
        );
        connection
            .execute(
                "UPDATE declared_sacrifices SET prev_hash = ?1, row_hash = ?2 WHERE rowid = ?3",
                params![previous.as_str(), row_hash.as_str(), rowid],
            )
            .map_err(|source| LegitimacyError::Sqlite {
                context: "updating declared sacrifice chain backfill".to_string(),
                source,
            })?;
        previous = row_hash;
    }

    Ok(())
}

pub(super) fn backfill_paradox_results_chain(
    connection: &Connection,
) -> Result<(), LegitimacyError> {
    let mut statement = connection
        .prepare(
            "SELECT rowid, rule_name, paradox_type, description, detected_at
             FROM paradox_results
             ORDER BY rowid ASC",
        )
        .map_err(|source| LegitimacyError::Sqlite {
            context: "preparing paradox chain backfill".to_string(),
            source,
        })?;
    let rows = statement
        .query_map([], |row| {
            Ok((
                row.get::<_, i64>(0)?,
                row.get::<_, String>(1)?,
                row.get::<_, String>(2)?,
                row.get::<_, String>(3)?,
                row.get::<_, String>(4)?,
            ))
        })
        .map_err(|source| LegitimacyError::Sqlite {
            context: "running paradox chain backfill".to_string(),
            source,
        })?;

    let mut previous = String::new();
    for row in rows {
        let (rowid, rule_name, paradox_type, description, detected_at) =
            row.map_err(|source| LegitimacyError::Sqlite {
                context: "reading paradox chain backfill row".to_string(),
                source,
            })?;
        let row_hash = chain_hash(
            previous.as_str(),
            rowid,
            paradox_result_content_json(
                rule_name.as_str(),
                paradox_type.as_str(),
                description.as_str(),
                detected_at.as_str(),
            )
            .as_str(),
        );
        connection
            .execute(
                "UPDATE paradox_results SET prev_hash = ?1, row_hash = ?2 WHERE rowid = ?3",
                params![previous.as_str(), row_hash.as_str(), rowid],
            )
            .map_err(|source| LegitimacyError::Sqlite {
                context: "updating paradox chain backfill".to_string(),
                source,
            })?;
        previous = row_hash;
    }

    Ok(())
}
