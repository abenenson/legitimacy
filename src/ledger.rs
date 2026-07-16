//! SQLite-backed audit ledger for historical legitimacy activity.

mod chain;

use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
    sync::{Mutex, OnceLock},
    time::Duration,
};

use rusqlite::{Connection, params};
use serde::{Deserialize, Serialize};

use crate::{
    Certificate, CompiledGovernanceKind, CompiledRule, DeclaredSacrificesCertificate,
    GovernanceProperty, LegitimacyError, MonitoringSpec, Rule, SacrificeProvenance, Verdict,
    paradox::{ParadoxType, ParadoxViolation},
};

use chain::{
    CERTIFICATES_TABLE, COMPILED_RULES_TABLE, DECLARED_SACRIFICES_TABLE,
    DeclaredSacrificeChainContent, certificate_content_json, compiled_rule_content_json,
    declared_sacrifice_content_json, ensure_chain_schema, insert_paradox_row, previous_hash,
    verify_chain,
};
pub use chain::{ChainVerificationResult, TableChainStatus};

const DEFAULT_LEDGER_DIR: &str = ".legitimacy";
const DEFAULT_LEDGER_FILE: &str = "ledger.sqlite3";

static LEDGER_LOCK: OnceLock<Mutex<()>> = OnceLock::new();

#[derive(Debug, Clone)]
pub struct Ledger {
    path: PathBuf,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct LedgerQuery {
    pub rule_name: Option<String>,
    pub rule_version: Option<String>,
    pub claimant_id: Option<String>,
    pub limit: usize,
}

impl LedgerQuery {
    #[tracing::instrument]
    pub fn with_limit(limit: usize) -> Self {
        Self {
            limit,
            ..Self::default()
        }
    }

    fn limit_or_default(&self) -> i64 {
        self.limit.max(1) as i64
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LedgerAuditReport {
    pub ledger_path: String,
    pub compiled_rules: Vec<CompiledRuleRecord>,
    pub certificates: Vec<CertificateRecord>,
    pub sacrifices: Vec<DeclaredSacrificeRecord>,
    pub paradox_results: Vec<ParadoxResultRecord>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompiledRuleRecord {
    pub name: String,
    pub version: String,
    pub admissible: bool,
    pub family_description: String,
    pub compiled_at: String,
    pub axiom_verdicts: Vec<Verdict>,
    pub strategyproofness: crate::StrategyproofnessVerdict,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CertificateRecord {
    pub rule_name: String,
    pub rule_version: String,
    pub compiled_rule_hash: String,
    pub claimant_id: String,
    pub outcome: f64,
    pub evidence: BTreeMap<String, String>,
    pub issued_at: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeclaredSacrificeRecord {
    pub compiled_kind: CompiledGovernanceKind,
    pub subject_name: String,
    pub subject_version: String,
    pub sacrificed_property: GovernanceProperty,
    pub justification: String,
    pub impact_bound: f64,
    pub monitoring_plan: Vec<MonitoringSpec>,
    pub provenance: SacrificeProvenance,
    pub declared_at: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ParadoxResultRecord {
    pub rule_name: String,
    pub paradox_type: String,
    pub description: String,
    pub detected_at: String,
}

impl Ledger {
    #[tracing::instrument]
    pub fn open_default() -> Result<Self, LegitimacyError> {
        Self::open(default_ledger_path()?)
    }

    #[tracing::instrument(skip(path))]
    pub fn open(path: impl Into<PathBuf>) -> Result<Self, LegitimacyError> {
        let ledger = Self { path: path.into() };
        ledger.with_connection(|_| Ok(()))?;
        Ok(ledger)
    }

    #[tracing::instrument(skip(self))]
    pub fn path(&self) -> &Path {
        &self.path
    }

    #[tracing::instrument(skip(self, compiled_rule))]
    pub fn record_compiled_rule(
        &self,
        compiled_rule: &CompiledRule,
    ) -> Result<(), LegitimacyError> {
        let axiom_verdicts_json =
            serde_json::to_string(&compiled_rule.axiom_verdicts).map_err(|source| {
                LegitimacyError::Serialize {
                    context: "compiled rule axiom verdicts".to_string(),
                    source,
                }
            })?;
        let strategyproofness_json = serde_json::to_string(&compiled_rule.strategyproofness)
            .map_err(|source| LegitimacyError::Serialize {
                context: "compiled rule strategyproofness".to_string(),
                source,
            })?;
        let content_json = compiled_rule_content_json(
            compiled_rule.name.as_str(),
            compiled_rule.version.as_str(),
            compiled_rule.is_admissible(),
            compiled_rule.family_description.as_str(),
            compiled_rule.compiled_at.as_str(),
            axiom_verdicts_json.as_str(),
            strategyproofness_json.as_str(),
        );

        self.with_connection(|connection| {
            chain::run_in_immediate_transaction(connection, "recording compiled rule", |connection| {
                let prev_hash = previous_hash(connection, COMPILED_RULES_TABLE)?;
                connection
                    .execute(
                        "INSERT INTO compiled_rules
                         (name, version, admissible, family_description, compiled_at, axiom_verdicts_json, strategyproofness_json, prev_hash, row_hash)
                         VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, '')",
                        params![
                            compiled_rule.name.as_str(),
                            compiled_rule.version.as_str(),
                            compiled_rule.is_admissible(),
                            compiled_rule.family_description.as_str(),
                            compiled_rule.compiled_at.as_str(),
                            axiom_verdicts_json.as_str(),
                            strategyproofness_json.as_str(),
                            prev_hash.as_str()
                        ],
                    )
                    .map_err(|source| LegitimacyError::Sqlite {
                        context: "recording compiled rule".to_string(),
                        source,
                    })?;
                let rowid = connection.last_insert_rowid();
                let row_hash = chain::chain_hash(prev_hash.as_str(), rowid, content_json.as_str());
                connection
                    .execute(
                        "UPDATE compiled_rules SET row_hash = ?1 WHERE rowid = ?2",
                        params![row_hash.as_str(), rowid],
                    )
                    .map_err(|source| LegitimacyError::Sqlite {
                        context: "finalizing compiled rule hash".to_string(),
                        source,
                    })?;
                chain::update_chain_head(connection, COMPILED_RULES_TABLE, row_hash.as_str())?;
                Ok(())
            })
        })
    }

    #[tracing::instrument(skip(self, certificate))]
    pub fn record_certificate(&self, certificate: &Certificate) -> Result<(), LegitimacyError> {
        let evidence_json = serde_json::to_string(&certificate.evidence).map_err(|source| {
            LegitimacyError::Serialize {
                context: "certificate evidence".to_string(),
                source,
            }
        })?;
        let content_json = certificate_content_json(
            certificate.rule_name.as_str(),
            certificate.rule_version.as_str(),
            certificate.compiled_rule_hash.as_str(),
            certificate.claimant_id.as_str(),
            certificate.outcome,
            evidence_json.as_str(),
            certificate.issued_at.as_str(),
        );

        self.with_connection(|connection| {
            chain::run_in_immediate_transaction(connection, "recording certificate", |connection| {
                let prev_hash = previous_hash(connection, CERTIFICATES_TABLE)?;
                connection
                    .execute(
                        "INSERT INTO certificates
                         (rule_name, rule_version, compiled_rule_hash, claimant_id, outcome, evidence_json, issued_at, prev_hash, row_hash)
                         VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, '')",
                        params![
                            certificate.rule_name.as_str(),
                            certificate.rule_version.as_str(),
                            certificate.compiled_rule_hash.as_str(),
                            certificate.claimant_id.as_str(),
                            certificate.outcome,
                            evidence_json.as_str(),
                            certificate.issued_at.as_str(),
                            prev_hash.as_str()
                        ],
                    )
                    .map_err(|source| LegitimacyError::Sqlite {
                        context: "recording certificate".to_string(),
                        source,
                    })?;
                let rowid = connection.last_insert_rowid();
                let row_hash = chain::chain_hash(prev_hash.as_str(), rowid, content_json.as_str());
                connection
                    .execute(
                        "UPDATE certificates SET row_hash = ?1 WHERE rowid = ?2",
                        params![row_hash.as_str(), rowid],
                    )
                    .map_err(|source| LegitimacyError::Sqlite {
                        context: "finalizing certificate hash".to_string(),
                        source,
                    })?;
                chain::update_chain_head(connection, CERTIFICATES_TABLE, row_hash.as_str())?;
                Ok(())
            })
        })
    }

    #[tracing::instrument(skip(self, certificate))]
    pub fn record_declared_sacrifices(
        &self,
        certificate: &DeclaredSacrificesCertificate,
    ) -> Result<(), LegitimacyError> {
        let compiled_kind = compiled_kind_label(certificate.compiled.kind());
        let subject_name = certificate.compiled.name().to_string();
        let subject_version = certificate.compiled.version().to_string();
        let declared_at = current_timestamp()?;

        self.with_connection(|connection| {
            chain::run_in_immediate_transaction(
                connection,
                "recording declared sacrifices",
                |connection| {
                    for sacrifice in &certificate.sacrifices {
                        let monitoring_plan_json = serde_json::to_string(&sacrifice.monitoring_plan)
                            .map_err(|source| LegitimacyError::Serialize {
                                context: "declared sacrifice monitoring plan".to_string(),
                                source,
                            })?;
                        let provenance_json = serde_json::to_string(&sacrifice.provenance)
                            .map_err(|source| LegitimacyError::Serialize {
                                context: "declared sacrifice provenance".to_string(),
                                source,
                            })?;
                        let content_json = declared_sacrifice_content_json(
                            &DeclaredSacrificeChainContent {
                                compiled_kind,
                                subject_name: subject_name.as_str(),
                                subject_version: subject_version.as_str(),
                                sacrificed_property: sacrifice.sacrificed_property.as_str(),
                                justification: sacrifice.justification.as_str(),
                                impact_bound: sacrifice.impact_bound,
                                monitoring_plan_json: monitoring_plan_json.as_str(),
                                provenance_json: provenance_json.as_str(),
                                declared_at: declared_at.as_str(),
                            },
                        );
                        let prev_hash = previous_hash(connection, DECLARED_SACRIFICES_TABLE)?;
                        connection
                            .execute(
                                "INSERT INTO declared_sacrifices
                                 (compiled_kind, subject_name, subject_version, sacrificed_property, justification, impact_bound, monitoring_plan_json, provenance_json, declared_at, prev_hash, row_hash)
                                 VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, '')",
                                params![
                                    compiled_kind,
                                    subject_name.as_str(),
                                    subject_version.as_str(),
                                    sacrifice.sacrificed_property.as_str(),
                                    sacrifice.justification.as_str(),
                                    sacrifice.impact_bound,
                                    monitoring_plan_json.as_str(),
                                    provenance_json.as_str(),
                                    declared_at.as_str(),
                                    prev_hash.as_str()
                                ],
                            )
                            .map_err(|source| LegitimacyError::Sqlite {
                                context: "recording declared sacrifice".to_string(),
                                source,
                            })?;
                        let rowid = connection.last_insert_rowid();
                        let row_hash =
                            chain::chain_hash(prev_hash.as_str(), rowid, content_json.as_str());
                        connection
                            .execute(
                                "UPDATE declared_sacrifices SET row_hash = ?1 WHERE rowid = ?2",
                                params![row_hash.as_str(), rowid],
                            )
                            .map_err(|source| LegitimacyError::Sqlite {
                                context: "finalizing declared sacrifice hash".to_string(),
                                source,
                            })?;
                        chain::update_chain_head(
                            connection,
                            DECLARED_SACRIFICES_TABLE,
                            row_hash.as_str(),
                        )?;
                    }

                    Ok(())
                },
            )
        })
    }

    #[tracing::instrument(skip(self, rule, violations))]
    pub fn record_paradox_results(
        &self,
        rule: &Rule,
        violations: &[ParadoxViolation],
    ) -> Result<(), LegitimacyError> {
        self.with_connection(|connection| {
            if violations.is_empty() {
                let detected_at = current_timestamp()?;
                insert_paradox_row(
                    connection,
                    rule.name.as_str(),
                    "none",
                    "No paradox violations detected",
                    detected_at.as_str(),
                )?;
                return Ok(());
            }

            for violation in violations {
                let detected_at = current_timestamp()?;
                insert_paradox_row(
                    connection,
                    rule.name.as_str(),
                    paradox_type_label(&violation.paradox_type),
                    violation.description.as_str(),
                    detected_at.as_str(),
                )?;
            }

            Ok(())
        })
    }

    #[tracing::instrument(skip(self, query))]
    pub fn audit(&self, query: &LedgerQuery) -> Result<LedgerAuditReport, LegitimacyError> {
        self.with_connection(|connection| {
            // Wrap the four cross-table reads in a deferred (read-only)
            // transaction so every load_* query observes a single
            // consistent SQLite snapshot. Without this, a concurrent
            // writer in another process can commit an atomic
            // INSERT-and-chain-head-bump between two of these
            // auto-commit reads, exposing only half of the writer's
            // transaction (e.g., the new certificate row but not the
            // matching paradox_results row written in the same logical
            // operation) and producing a torn audit report.
            chain::run_in_deferred_transaction(connection, "auditing ledger", |connection| {
                Ok(LedgerAuditReport {
                    ledger_path: self.path.display().to_string(),
                    compiled_rules: load_compiled_rules(connection, query)?,
                    certificates: load_certificates(connection, query)?,
                    sacrifices: load_declared_sacrifices(connection, query)?,
                    paradox_results: load_paradox_results(connection, query)?,
                })
            })
        })
    }

    #[tracing::instrument(skip(self))]
    pub fn verify_chain(&self) -> Result<ChainVerificationResult, LegitimacyError> {
        self.with_connection(verify_chain)
    }

    fn with_connection<T>(
        &self,
        f: impl FnOnce(&Connection) -> Result<T, LegitimacyError>,
    ) -> Result<T, LegitimacyError> {
        let guard = LEDGER_LOCK.get_or_init(|| Mutex::new(())).lock();
        let _guard = match guard {
            Ok(guard) => guard,
            Err(poisoned) => poisoned.into_inner(),
        };

        if let Some(parent) = self.path.parent() {
            fs::create_dir_all(parent).map_err(|source| LegitimacyError::Io {
                context: format!("creating ledger directory '{}'", parent.display()),
                source,
            })?;
        }

        let connection =
            Connection::open(&self.path).map_err(|source| LegitimacyError::Sqlite {
                context: format!("opening ledger '{}'", self.path.display()),
                source,
            })?;
        connection
            .busy_timeout(Duration::from_secs(5))
            .map_err(|source| LegitimacyError::Sqlite {
                context: "setting ledger busy timeout".to_string(),
                source,
            })?;
        connection
            .pragma_update(None, "journal_mode", "WAL")
            .map_err(|source| LegitimacyError::Sqlite {
                context: "enabling ledger WAL mode".to_string(),
                source,
            })?;
        connection
            .execute_batch(
                "CREATE TABLE IF NOT EXISTS compiled_rules (
                    name TEXT NOT NULL,
                    version TEXT NOT NULL,
                    admissible INTEGER NOT NULL,
                    family_description TEXT NOT NULL,
                    compiled_at TEXT NOT NULL,
                    axiom_verdicts_json TEXT NOT NULL,
                    strategyproofness_json TEXT NOT NULL DEFAULT '\"Strategyproof\"',
                    prev_hash TEXT NOT NULL DEFAULT '',
                    row_hash TEXT NOT NULL DEFAULT ''
                );
                CREATE TABLE IF NOT EXISTS certificates (
                    rule_name TEXT NOT NULL,
                    rule_version TEXT NOT NULL,
                    compiled_rule_hash TEXT NOT NULL DEFAULT '',
                    claimant_id TEXT NOT NULL,
                    outcome REAL NOT NULL,
                    evidence_json TEXT NOT NULL,
                    issued_at TEXT NOT NULL,
                    prev_hash TEXT NOT NULL DEFAULT '',
                    row_hash TEXT NOT NULL DEFAULT ''
                );
                CREATE TABLE IF NOT EXISTS declared_sacrifices (
                    compiled_kind TEXT NOT NULL,
                    subject_name TEXT NOT NULL,
                    subject_version TEXT NOT NULL,
                    sacrificed_property TEXT NOT NULL,
                    justification TEXT NOT NULL,
                    impact_bound REAL NOT NULL,
                    monitoring_plan_json TEXT NOT NULL,
                    provenance_json TEXT NOT NULL,
                    declared_at TEXT NOT NULL,
                    prev_hash TEXT NOT NULL DEFAULT '',
                    row_hash TEXT NOT NULL DEFAULT ''
                );
                CREATE TABLE IF NOT EXISTS paradox_results (
                    rule_name TEXT NOT NULL,
                    paradox_type TEXT NOT NULL,
                    description TEXT NOT NULL,
                    detected_at TEXT NOT NULL,
                    prev_hash TEXT NOT NULL DEFAULT '',
                    row_hash TEXT NOT NULL DEFAULT ''
                );",
            )
            .map_err(|source| LegitimacyError::Sqlite {
                context: "creating ledger schema".to_string(),
                source,
            })?;
        ensure_column(
            &connection,
            "compiled_rules",
            "strategyproofness_json",
            "TEXT NOT NULL DEFAULT '\"Strategyproof\"'",
        )?;
        ensure_column(
            &connection,
            "certificates",
            "compiled_rule_hash",
            "TEXT NOT NULL DEFAULT ''",
        )?;
        ensure_chain_schema(&connection)?;

        f(&connection)
    }
}

fn ensure_column(
    connection: &Connection,
    table: &str,
    column: &str,
    definition: &str,
) -> Result<(), LegitimacyError> {
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
    for row in rows {
        if row.map_err(|source| LegitimacyError::Sqlite {
            context: format!("reading schema row for '{table}'"),
            source,
        })? == column
        {
            return Ok(());
        }
    }

    connection
        .execute(
            &format!("ALTER TABLE {table} ADD COLUMN {column} {definition}"),
            [],
        )
        .map_err(|source| LegitimacyError::Sqlite {
            context: format!("adding {column} column to '{table}'"),
            source,
        })?;
    Ok(())
}

fn load_compiled_rules(
    connection: &Connection,
    query: &LedgerQuery,
) -> Result<Vec<CompiledRuleRecord>, LegitimacyError> {
    let mut statement = connection
        .prepare(
            "SELECT name, version, admissible, family_description, compiled_at, axiom_verdicts_json, strategyproofness_json
             FROM compiled_rules
             WHERE (?1 IS NULL OR name = ?1)
               AND (?2 IS NULL OR version = ?2)
             ORDER BY rowid DESC
             LIMIT ?3",
        )
        .map_err(|source| LegitimacyError::Sqlite {
            context: "preparing compiled rule audit query".to_string(),
            source,
        })?;

    let rows = statement
        .query_map(
            params![
                query.rule_name.as_deref(),
                query.rule_version.as_deref(),
                query.limit_or_default()
            ],
            |row| {
                Ok((
                    row.get::<_, String>(0)?,
                    row.get::<_, String>(1)?,
                    row.get::<_, bool>(2)?,
                    row.get::<_, String>(3)?,
                    row.get::<_, String>(4)?,
                    row.get::<_, String>(5)?,
                    row.get::<_, String>(6)?,
                ))
            },
        )
        .map_err(|source| LegitimacyError::Sqlite {
            context: "running compiled rule audit query".to_string(),
            source,
        })?;

    let mut records = Vec::new();
    for row in rows {
        let (
            name,
            version,
            admissible,
            family_description,
            compiled_at,
            axiom_verdicts_json,
            strategyproofness_json,
        ) = row.map_err(|source| LegitimacyError::Sqlite {
            context: "reading compiled rule audit row".to_string(),
            source,
        })?;
        let axiom_verdicts =
            serde_json::from_str(&axiom_verdicts_json).map_err(|source| LegitimacyError::Json {
                context: "ledger compiled rule axiom verdicts".to_string(),
                source,
            })?;
        let strategyproofness =
            serde_json::from_str(&strategyproofness_json).map_err(|source| {
                LegitimacyError::Json {
                    context: "ledger compiled rule strategyproofness".to_string(),
                    source,
                }
            })?;
        records.push(CompiledRuleRecord {
            name,
            version,
            admissible,
            family_description,
            compiled_at,
            axiom_verdicts,
            strategyproofness,
        });
    }

    Ok(records)
}

fn load_certificates(
    connection: &Connection,
    query: &LedgerQuery,
) -> Result<Vec<CertificateRecord>, LegitimacyError> {
    let mut statement = connection
        .prepare(
            "SELECT rule_name, rule_version, compiled_rule_hash, claimant_id, outcome, evidence_json, issued_at
             FROM certificates
             WHERE (?1 IS NULL OR rule_name = ?1)
               AND (?2 IS NULL OR rule_version = ?2)
               AND (?3 IS NULL OR claimant_id = ?3)
             ORDER BY rowid DESC
             LIMIT ?4",
        )
        .map_err(|source| LegitimacyError::Sqlite {
            context: "preparing certificate audit query".to_string(),
            source,
        })?;

    let rows = statement
        .query_map(
            params![
                query.rule_name.as_deref(),
                query.rule_version.as_deref(),
                query.claimant_id.as_deref(),
                query.limit_or_default()
            ],
            |row| {
                Ok((
                    row.get::<_, String>(0)?,
                    row.get::<_, String>(1)?,
                    row.get::<_, String>(2)?,
                    row.get::<_, String>(3)?,
                    row.get::<_, f64>(4)?,
                    row.get::<_, String>(5)?,
                    row.get::<_, String>(6)?,
                ))
            },
        )
        .map_err(|source| LegitimacyError::Sqlite {
            context: "running certificate audit query".to_string(),
            source,
        })?;

    let mut records = Vec::new();
    for row in rows {
        let (
            rule_name,
            rule_version,
            compiled_rule_hash,
            claimant_id,
            outcome,
            evidence_json,
            issued_at,
        ) = row.map_err(|source| LegitimacyError::Sqlite {
            context: "reading certificate audit row".to_string(),
            source,
        })?;
        let evidence =
            serde_json::from_str(&evidence_json).map_err(|source| LegitimacyError::Json {
                context: "ledger certificate evidence".to_string(),
                source,
            })?;
        records.push(CertificateRecord {
            rule_name,
            rule_version,
            compiled_rule_hash,
            claimant_id,
            outcome,
            evidence,
            issued_at,
        });
    }

    Ok(records)
}

fn load_declared_sacrifices(
    connection: &Connection,
    query: &LedgerQuery,
) -> Result<Vec<DeclaredSacrificeRecord>, LegitimacyError> {
    let mut statement = connection
        .prepare(
            "SELECT compiled_kind, subject_name, subject_version, sacrificed_property, justification, impact_bound, monitoring_plan_json, provenance_json, declared_at
             FROM declared_sacrifices
             WHERE (?1 IS NULL OR subject_name = ?1)
               AND (?2 IS NULL OR subject_version = ?2)
             ORDER BY rowid DESC
             LIMIT ?3",
        )
        .map_err(|source| LegitimacyError::Sqlite {
            context: "preparing declared sacrifice audit query".to_string(),
            source,
        })?;

    let rows = statement
        .query_map(
            params![
                query.rule_name.as_deref(),
                query.rule_version.as_deref(),
                query.limit_or_default()
            ],
            |row| {
                Ok((
                    row.get::<_, String>(0)?,
                    row.get::<_, String>(1)?,
                    row.get::<_, String>(2)?,
                    row.get::<_, String>(3)?,
                    row.get::<_, String>(4)?,
                    row.get::<_, f64>(5)?,
                    row.get::<_, String>(6)?,
                    row.get::<_, String>(7)?,
                    row.get::<_, String>(8)?,
                ))
            },
        )
        .map_err(|source| LegitimacyError::Sqlite {
            context: "running declared sacrifice audit query".to_string(),
            source,
        })?;

    let mut records = Vec::new();
    for row in rows {
        let (
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
            context: "reading declared sacrifice audit row".to_string(),
            source,
        })?;
        let monitoring_plan = serde_json::from_str(&monitoring_plan_json).map_err(|source| {
            LegitimacyError::Json {
                context: "ledger declared sacrifice monitoring plan".to_string(),
                source,
            }
        })?;
        let provenance =
            serde_json::from_str(&provenance_json).map_err(|source| LegitimacyError::Json {
                context: "ledger declared sacrifice provenance".to_string(),
                source,
            })?;
        records.push(DeclaredSacrificeRecord {
            compiled_kind: parse_compiled_kind(&compiled_kind)?,
            subject_name,
            subject_version,
            sacrificed_property: parse_governance_property(&sacrificed_property)?,
            justification,
            impact_bound,
            monitoring_plan,
            provenance,
            declared_at,
        });
    }

    Ok(records)
}

fn load_paradox_results(
    connection: &Connection,
    query: &LedgerQuery,
) -> Result<Vec<ParadoxResultRecord>, LegitimacyError> {
    let mut statement = connection
        .prepare(
            "SELECT rule_name, paradox_type, description, detected_at
             FROM paradox_results
             WHERE (?1 IS NULL OR rule_name = ?1)
             ORDER BY rowid DESC
             LIMIT ?2",
        )
        .map_err(|source| LegitimacyError::Sqlite {
            context: "preparing paradox audit query".to_string(),
            source,
        })?;

    let rows = statement
        .query_map(
            params![query.rule_name.as_deref(), query.limit_or_default()],
            |row| {
                Ok(ParadoxResultRecord {
                    rule_name: row.get(0)?,
                    paradox_type: row.get(1)?,
                    description: row.get(2)?,
                    detected_at: row.get(3)?,
                })
            },
        )
        .map_err(|source| LegitimacyError::Sqlite {
            context: "running paradox audit query".to_string(),
            source,
        })?;

    let mut records = Vec::new();
    for row in rows {
        records.push(row.map_err(|source| LegitimacyError::Sqlite {
            context: "reading paradox audit row".to_string(),
            source,
        })?);
    }

    Ok(records)
}

fn default_ledger_path() -> Result<PathBuf, LegitimacyError> {
    let cwd = std::env::current_dir().map_err(|source| LegitimacyError::Io {
        context: "determining current directory for ledger".to_string(),
        source,
    })?;

    let root = cwd
        .ancestors()
        .find(|path| path.join("Cargo.toml").exists())
        .unwrap_or(cwd.as_path());

    Ok(root.join(DEFAULT_LEDGER_DIR).join(DEFAULT_LEDGER_FILE))
}

fn compiled_kind_label(kind: CompiledGovernanceKind) -> &'static str {
    match kind {
        CompiledGovernanceKind::Rule => "rule",
        CompiledGovernanceKind::Graph => "graph",
    }
}

fn parse_compiled_kind(value: &str) -> Result<CompiledGovernanceKind, LegitimacyError> {
    match value {
        "rule" => Ok(CompiledGovernanceKind::Rule),
        "graph" => Ok(CompiledGovernanceKind::Graph),
        other => Err(LegitimacyError::invalid_input(format!(
            "unknown compiled governance kind '{other}' in ledger"
        ))),
    }
}

fn parse_governance_property(value: &str) -> Result<GovernanceProperty, LegitimacyError> {
    match value {
        "consistency" => Ok(GovernanceProperty::Consistency),
        "solidarity" => Ok(GovernanceProperty::Solidarity),
        "monotonicity" => Ok(GovernanceProperty::Monotonicity),
        "strategyproofness" => Ok(GovernanceProperty::Strategyproofness),
        "certifiability" => Ok(GovernanceProperty::Certifiability),
        "observable_determinacy" => Ok(GovernanceProperty::ObservableDeterminacy),
        "corrigibility" => Ok(GovernanceProperty::Corrigibility),
        "compositional_safety" => Ok(GovernanceProperty::CompositionalSafety),
        "non_vacuous" | "nonvacuous" => Ok(GovernanceProperty::NonVacuous),
        other => Err(LegitimacyError::invalid_input(format!(
            "unknown governance property '{other}' in ledger"
        ))),
    }
}

fn paradox_type_label(paradox_type: &ParadoxType) -> &'static str {
    match paradox_type {
        ParadoxType::ClaimantAddition => "claimant_addition",
        ParadoxType::Population => "population",
        ParadoxType::Priority => "priority",
    }
}

fn current_timestamp() -> Result<String, LegitimacyError> {
    let seconds = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)?
        .as_secs() as i64;
    let days = seconds.div_euclid(86_400);
    let seconds_of_day = seconds.rem_euclid(86_400);
    let (year, month, day) = civil_from_days(days);
    let hour = seconds_of_day / 3_600;
    let minute = (seconds_of_day % 3_600) / 60;
    let second = seconds_of_day % 60;

    Ok(format!(
        "{year:04}-{month:02}-{day:02}T{hour:02}:{minute:02}:{second:02}Z"
    ))
}

fn civil_from_days(days_since_unix_epoch: i64) -> (i32, u32, u32) {
    let shifted_days = days_since_unix_epoch + 719_468;
    let era = if shifted_days >= 0 {
        shifted_days
    } else {
        shifted_days - 146_096
    } / 146_097;
    let day_of_era = shifted_days - era * 146_097;
    let year_of_era =
        (day_of_era - day_of_era / 1_460 + day_of_era / 36_524 - day_of_era / 146_096) / 365;
    let year = year_of_era + era * 400;
    let day_of_year = day_of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100);
    let month_piece = (5 * day_of_year + 2) / 153;
    let day = day_of_year - (153 * month_piece + 2) / 5 + 1;
    let month = month_piece + if month_piece < 10 { 3 } else { -9 };
    let year = year + if month <= 2 { 1 } else { 0 };

    (year as i32, month as u32, day as u32)
}
