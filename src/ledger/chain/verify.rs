use rusqlite::Connection;

use crate::LegitimacyError;

use super::{
    CERTIFICATES_TABLE, COMPILED_RULES_TABLE, DECLARED_SACRIFICES_TABLE,
    DeclaredSacrificeChainContent, PARADOX_RESULTS_TABLE, TableChainStatus,
    certificate_content_json, chain_hash, compiled_rule_content_json,
    declared_sacrifice_content_json, invalid_table_status, legacy_certificate_content_json,
    legacy_compiled_rule_content_json, valid_table_status, verify_chain_head,
};

pub(super) fn verify_compiled_rules_chain(
    connection: &Connection,
) -> Result<TableChainStatus, LegitimacyError> {
    let mut statement = connection
        .prepare(
            "SELECT rowid, name, version, admissible, family_description, compiled_at, axiom_verdicts_json, strategyproofness_json, prev_hash, row_hash
             FROM compiled_rules
             ORDER BY rowid ASC",
        )
        .map_err(|source| LegitimacyError::Sqlite {
            context: "preparing compiled rule chain verification".to_string(),
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
                row.get::<_, String>(8)?,
                row.get::<_, String>(9)?,
            ))
        })
        .map_err(|source| LegitimacyError::Sqlite {
            context: "running compiled rule chain verification".to_string(),
            source,
        })?;

    let mut previous = String::new();
    let mut checked_rows = 0usize;
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
            prev_hash,
            row_hash,
        ) = row.map_err(|source| LegitimacyError::Sqlite {
            context: "reading compiled rule chain verification row".to_string(),
            source,
        })?;
        if prev_hash != previous {
            return Ok(invalid_table_status(
                COMPILED_RULES_TABLE,
                checked_rows,
                format!("rowid {rowid} has mismatched prev_hash"),
            ));
        }
        let expected = chain_hash(
            prev_hash.as_str(),
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
        let legacy_expected = (strategyproofness_json == "\"Strategyproof\"").then(|| {
            chain_hash(
                prev_hash.as_str(),
                rowid,
                legacy_compiled_rule_content_json(
                    name.as_str(),
                    version.as_str(),
                    admissible,
                    family_description.as_str(),
                    compiled_at.as_str(),
                    axiom_verdicts_json.as_str(),
                )
                .as_str(),
            )
        });
        if row_hash != expected && legacy_expected.as_deref() != Some(row_hash.as_str()) {
            return Ok(invalid_table_status(
                COMPILED_RULES_TABLE,
                checked_rows,
                format!("rowid {rowid} has mismatched row_hash"),
            ));
        }
        previous = row_hash;
        checked_rows += 1;
    }

    if let Some(status) = verify_chain_head(
        connection,
        COMPILED_RULES_TABLE,
        checked_rows,
        previous.as_str(),
    )? {
        return Ok(status);
    }

    Ok(valid_table_status(COMPILED_RULES_TABLE, checked_rows))
}

pub(super) fn verify_certificates_chain(
    connection: &Connection,
) -> Result<TableChainStatus, LegitimacyError> {
    let mut statement = connection
        .prepare(
            "SELECT rowid, rule_name, rule_version, compiled_rule_hash, claimant_id, outcome, evidence_json, issued_at, prev_hash, row_hash
             FROM certificates
             ORDER BY rowid ASC",
        )
        .map_err(|source| LegitimacyError::Sqlite {
            context: "preparing certificate chain verification".to_string(),
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
                row.get::<_, String>(8)?,
                row.get::<_, String>(9)?,
            ))
        })
        .map_err(|source| LegitimacyError::Sqlite {
            context: "running certificate chain verification".to_string(),
            source,
        })?;

    let mut previous = String::new();
    let mut checked_rows = 0usize;
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
            prev_hash,
            row_hash,
        ) = row.map_err(|source| LegitimacyError::Sqlite {
            context: "reading certificate chain verification row".to_string(),
            source,
        })?;
        if prev_hash != previous {
            return Ok(invalid_table_status(
                CERTIFICATES_TABLE,
                checked_rows,
                format!("rowid {rowid} has mismatched prev_hash"),
            ));
        }
        let expected = chain_hash(
            prev_hash.as_str(),
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
        let legacy_expected = if compiled_rule_hash.is_empty() {
            Some(chain_hash(
                prev_hash.as_str(),
                rowid,
                legacy_certificate_content_json(
                    rule_name.as_str(),
                    rule_version.as_str(),
                    claimant_id.as_str(),
                    outcome,
                    evidence_json.as_str(),
                    issued_at.as_str(),
                )
                .as_str(),
            ))
        } else {
            None
        };
        if row_hash != expected && legacy_expected.as_deref() != Some(row_hash.as_str()) {
            return Ok(invalid_table_status(
                CERTIFICATES_TABLE,
                checked_rows,
                format!("rowid {rowid} has mismatched row_hash"),
            ));
        }
        previous = row_hash;
        checked_rows += 1;
    }

    if let Some(status) = verify_chain_head(
        connection,
        CERTIFICATES_TABLE,
        checked_rows,
        previous.as_str(),
    )? {
        return Ok(status);
    }

    Ok(valid_table_status(CERTIFICATES_TABLE, checked_rows))
}

pub(super) fn verify_declared_sacrifices_chain(
    connection: &Connection,
) -> Result<TableChainStatus, LegitimacyError> {
    let mut statement = connection
        .prepare(
            "SELECT rowid, compiled_kind, subject_name, subject_version, sacrificed_property, justification, impact_bound, monitoring_plan_json, provenance_json, declared_at, prev_hash, row_hash
             FROM declared_sacrifices
             ORDER BY rowid ASC",
        )
        .map_err(|source| LegitimacyError::Sqlite {
            context: "preparing declared sacrifice chain verification".to_string(),
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
                row.get::<_, String>(10)?,
                row.get::<_, String>(11)?,
            ))
        })
        .map_err(|source| LegitimacyError::Sqlite {
            context: "running declared sacrifice chain verification".to_string(),
            source,
        })?;

    let mut previous = String::new();
    let mut checked_rows = 0usize;
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
            prev_hash,
            row_hash,
        ) = row.map_err(|source| LegitimacyError::Sqlite {
            context: "reading declared sacrifice chain verification row".to_string(),
            source,
        })?;
        if prev_hash != previous {
            return Ok(invalid_table_status(
                DECLARED_SACRIFICES_TABLE,
                checked_rows,
                format!("rowid {rowid} has mismatched prev_hash"),
            ));
        }
        let expected = chain_hash(
            prev_hash.as_str(),
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
        if row_hash != expected {
            return Ok(invalid_table_status(
                DECLARED_SACRIFICES_TABLE,
                checked_rows,
                format!("rowid {rowid} has mismatched row_hash"),
            ));
        }
        previous = row_hash;
        checked_rows += 1;
    }

    if let Some(status) = verify_chain_head(
        connection,
        DECLARED_SACRIFICES_TABLE,
        checked_rows,
        previous.as_str(),
    )? {
        return Ok(status);
    }

    Ok(valid_table_status(DECLARED_SACRIFICES_TABLE, checked_rows))
}

pub(super) fn verify_paradox_results_chain(
    connection: &Connection,
) -> Result<TableChainStatus, LegitimacyError> {
    let mut statement = connection
        .prepare(
            "SELECT rowid, rule_name, paradox_type, description, detected_at, prev_hash, row_hash
             FROM paradox_results
             ORDER BY rowid ASC",
        )
        .map_err(|source| LegitimacyError::Sqlite {
            context: "preparing paradox chain verification".to_string(),
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
                row.get::<_, String>(6)?,
            ))
        })
        .map_err(|source| LegitimacyError::Sqlite {
            context: "running paradox chain verification".to_string(),
            source,
        })?;

    let mut previous = String::new();
    let mut checked_rows = 0usize;
    for row in rows {
        let (rowid, rule_name, paradox_type, description, detected_at, prev_hash, row_hash) =
            row.map_err(|source| LegitimacyError::Sqlite {
                context: "reading paradox chain verification row".to_string(),
                source,
            })?;
        if prev_hash != previous {
            return Ok(invalid_table_status(
                PARADOX_RESULTS_TABLE,
                checked_rows,
                format!("rowid {rowid} has mismatched prev_hash"),
            ));
        }
        let expected = chain_hash(
            prev_hash.as_str(),
            rowid,
            super::paradox_result_content_json(
                rule_name.as_str(),
                paradox_type.as_str(),
                description.as_str(),
                detected_at.as_str(),
            )
            .as_str(),
        );
        if row_hash != expected {
            return Ok(invalid_table_status(
                PARADOX_RESULTS_TABLE,
                checked_rows,
                format!("rowid {rowid} has mismatched row_hash"),
            ));
        }
        previous = row_hash;
        checked_rows += 1;
    }

    if let Some(status) = verify_chain_head(
        connection,
        PARADOX_RESULTS_TABLE,
        checked_rows,
        previous.as_str(),
    )? {
        return Ok(status);
    }

    Ok(valid_table_status(PARADOX_RESULTS_TABLE, checked_rows))
}
