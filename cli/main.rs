mod audit_graph;
mod commands;
mod corpus;
mod input;
mod protocol_support;
mod reporting;
#[cfg(test)]
mod tests;
mod witness;
use clap::Parser;
use commands::{
    AuditEvent, AuditResult, AuditStatus, Cli, Command, ComplianceReport, LedgerAuditOutput,
    ProtocolAuditOutput, ProtocolCommand,
};
use input::{load_claim_corpus, load_review_overlay};
use legitimacy::{
    BoundaryCausalSafetyAssessment, Certificate, CompileOptions, CompiledGovernance,
    ExtractionCoverageReport, FullConsistencyOptions, GovernanceExtractionArtifacts,
    LegitimacyError, ProtocolState,
    certificate::{CertificationContext, certify},
    cli_runtime::{RuntimeContext, RuntimeOptions, load_runtime_context_with_options},
    extract::{
        ExtractionOptions, analyze_extraction_with_review, audit_extracted_graph_with_review,
        extract_governance_artifacts_with_review, synthetic_claims,
    },
    factor::compute_factor_exposure_with_family_and_options,
    ledger::{Ledger, LedgerQuery},
    monitor::{
        GovernanceEventSource, MonitorSession, compiled_graph_from_rule,
        default_policy_event_source_path, monitor,
    },
    paradox::run_paradox_suite,
    policy::{parse_claude_dir, parse_graph_file},
    protocol::{
        activate as activate_protocol, compile as compile_protocol, measure as measure_protocol,
    },
};
use protocol_support::{protocol_error_to_verdict, protocol_ledger_view, verify_protocol_ledger};
use reporting::{
    pretty_json, print_compile_report, print_extraction_artifacts_report, print_extraction_report,
    print_graph_compile_report, print_paradox_report, print_protocol_status,
    print_sacrifice_report,
};
use std::{
    collections::BTreeMap,
    fs::{self, File},
    io::{BufRead, BufReader},
    path::Path,
    process::ExitCode,
};
use tracing_subscriber::EnvFilter;

fn main() -> ExitCode {
    init_tracing();
    match run() {
        Ok(code) => code,
        Err(err) => {
            eprintln!("legitimacy: {err}");
            ExitCode::FAILURE
        }
    }
}

fn init_tracing() {
    let filter = EnvFilter::builder()
        .with_default_directive(tracing_subscriber::filter::LevelFilter::WARN.into())
        .with_env_var("LEGITIMACY_LOG")
        .from_env_lossy();

    let _ = tracing_subscriber::fmt()
        .with_env_filter(filter)
        .with_target(true)
        .try_init();
}

fn consistency_options(allow_exponential_consistency: bool) -> FullConsistencyOptions {
    FullConsistencyOptions {
        allow_exponential_consistency,
        ..FullConsistencyOptions::default()
    }
}

fn runtime_options(allow_exponential_consistency: bool) -> RuntimeOptions {
    RuntimeOptions {
        compile: CompileOptions {
            consistency: consistency_options(allow_exponential_consistency),
        },
    }
}

fn run() -> Result<ExitCode, LegitimacyError> {
    let cli = Cli::parse();

    let Some(command) = cli.command else {
        return Err(LegitimacyError::invalid_input("missing subcommand"));
    };

    match command {
        Command::Compile {
            policy,
            allow_exponential_consistency,
        } => {
            match detect_policy_format(&policy)? {
                PolicyFormat::Rule => {
                    let context = load_runtime_context_with_options(
                        &policy,
                        runtime_options(allow_exponential_consistency),
                    )?;
                    print_compile_report(&context.compiled)?;
                }
                PolicyFormat::Graph => {
                    let spec = parse_graph_file(&policy)?;
                    let graph = spec.clone().try_into_graph(policy.display().to_string())?;
                    print_graph_compile_report(&spec, &graph)?;
                }
            }
            Ok(ExitCode::SUCCESS)
        }
        Command::Paradox {
            policy,
            allow_exponential_consistency,
        } => {
            let context = load_runtime_context_with_options(
                &policy,
                runtime_options(allow_exponential_consistency),
            )?;
            let violations = run_paradox_suite(
                &context.parsed.rule,
                &context.parsed.claims,
                &context.parsed.estate,
                &context.parsed.claimants,
            )?;
            print_paradox_report(&context.compiled, &violations)?;
            Ok(ExitCode::SUCCESS)
        }
        Command::Factor {
            policy,
            allow_exponential_consistency,
        } => {
            match detect_policy_format(&policy)? {
                PolicyFormat::Rule => {
                    let options = consistency_options(allow_exponential_consistency);
                    let context = load_runtime_context_with_options(
                        &policy,
                        runtime_options(allow_exponential_consistency),
                    )?;
                    let exposure = compute_factor_exposure_with_family_and_options(
                        &context.parsed.rule,
                        &context.parsed.claims,
                        &context.parsed.claimants,
                        &context.parsed.estate,
                        &context.parsed.family,
                        options,
                    )?;

                    println!(
                        "rule: {} v{}",
                        context.parsed.rule.name, context.parsed.rule.version
                    );
                    println!("{}", exposure.render_text_radar());
                }
                PolicyFormat::Graph => {
                    return Err(LegitimacyError::invalid_input(
                        "factor analysis currently requires a rule policy with concrete claims",
                    ));
                }
            }
            Ok(ExitCode::SUCCESS)
        }
        Command::Extract {
            source_dir,
            claude_dir,
            allow_partial,
            mode,
            emit_graph,
            emit_theorem_witness,
            theorem_name,
            review_overlay,
            claims,
            claims_provenance,
            synthetic,
        } => {
            if claude_dir {
                if emit_theorem_witness.is_some() {
                    return Err(LegitimacyError::invalid_input(
                        "--emit-theorem-witness requires source-code extraction, not --claude-dir",
                    ));
                }
                let graph = parse_claude_dir(&source_dir)?;
                if let Some(path) = emit_graph {
                    fs::write(
                        &path,
                        serde_json::to_vec_pretty(&graph).map_err(|source| {
                            LegitimacyError::Serialize {
                                context: format!("extracted graph '{}'", path.display()),
                                source,
                            }
                        })?,
                    )
                    .map_err(|source| LegitimacyError::Io {
                        context: format!("writing extracted graph '{}'", path.display()),
                        source,
                    })?;
                }
                let artifacts = GovernanceExtractionArtifacts {
                    source_dir: source_dir.display().to_string(),
                    graph,
                    coverage: ExtractionCoverageReport {
                        files_discovered: 1,
                        files_parsed: 1,
                        files_skipped: 0,
                        files_errored: 0,
                        complete: true,
                        files: Vec::new(),
                    },
                    recognized_nodes: Vec::new(),
                    recognized_edges: Vec::new(),
                    resolution_issues: Vec::new(),
                    review_overlay: None,
                    boundary_causal_safety: BoundaryCausalSafetyAssessment::default(),
                };
                if let Some(claims_path) = claims {
                    let corpus = load_claim_corpus(&claims_path)?;
                    let audit = legitimacy::audit_governance_graph(
                        &artifacts.graph,
                        corpus,
                        claims_provenance.into(),
                        BoundaryCausalSafetyAssessment::default(),
                    )?;
                    print_extraction_report(&legitimacy::GovernanceExtractionReport {
                        artifacts,
                        audit,
                    })?;
                } else if synthetic {
                    let audit = legitimacy::audit_governance_graph(
                        &artifacts.graph,
                        synthetic_claims(&artifacts.graph),
                        legitimacy::ClaimCorpusProvenance::SyntheticStructuralProbe,
                        BoundaryCausalSafetyAssessment::default(),
                    )?;
                    print_extraction_report(&legitimacy::GovernanceExtractionReport {
                        artifacts,
                        audit,
                    })?;
                } else {
                    print_extraction_artifacts_report(&artifacts)?;
                }
                return Ok(ExitCode::SUCCESS);
            }
            let options = ExtractionOptions {
                allow_partial,
                mode: mode.into(),
            };
            let review_overlay = review_overlay
                .as_ref()
                .map(|path| load_review_overlay(path))
                .transpose()?;
            let artifacts = extract_governance_artifacts_with_review(
                &source_dir,
                options,
                review_overlay.as_ref(),
            )?;
            if let Some(path) = emit_graph {
                fs::write(
                    &path,
                    serde_json::to_vec_pretty(&artifacts.graph).map_err(|source| {
                        LegitimacyError::Serialize {
                            context: format!("extracted graph '{}'", path.display()),
                            source,
                        }
                    })?,
                )
                .map_err(|source| LegitimacyError::Io {
                    context: format!("writing extracted graph '{}'", path.display()),
                    source,
                })?;
            }
            if let Some(path) = emit_theorem_witness {
                witness::write_ast_theorem_witness(
                    &path,
                    &source_dir,
                    &artifacts.graph,
                    &theorem_name,
                )?;
            }

            if let Some(claims_path) = claims {
                let corpus = load_claim_corpus(&claims_path)?;
                let report = audit_extracted_graph_with_review(
                    &source_dir,
                    corpus,
                    options,
                    claims_provenance.into(),
                    review_overlay.as_ref(),
                )?;
                print_extraction_report(&report)?;
            } else if synthetic {
                let report =
                    analyze_extraction_with_review(&source_dir, options, review_overlay.as_ref())?;
                print_extraction_report(&report)?;
            } else {
                print_extraction_artifacts_report(&artifacts)?;
            }
            Ok(ExitCode::SUCCESS)
        }
        Command::AuditGraph(command) => audit_graph::run(command),
        Command::VerifyWitness(command) => witness::run(command),
        Command::Sacrifice {
            policy,
            allow_exponential_consistency,
        } => {
            match detect_policy_format(&policy)? {
                PolicyFormat::Rule => {
                    let context = load_runtime_context_with_options(
                        &policy,
                        runtime_options(allow_exponential_consistency),
                    )?;
                    let certificate = legitimacy::compile_with_sacrifices_with_family_and_options(
                        &context.parsed.rule,
                        &context.parsed.claims,
                        &context.parsed.claimants,
                        &context.parsed.estate,
                        &context.parsed.family,
                        runtime_options(allow_exponential_consistency).compile,
                    )?;
                    print_sacrifice_report(&certificate);
                }
                PolicyFormat::Graph => {
                    return Err(LegitimacyError::invalid_input(
                        "sacrifice analysis currently requires a rule policy with concrete claims",
                    ));
                }
            }
            Ok(ExitCode::SUCCESS)
        }
        Command::Monitor {
            policy,
            allow_exponential_consistency,
            interval,
        } => {
            let session =
                monitor_session_for_policy(&policy, interval, allow_exponential_consistency)?;
            let event_source_path = default_policy_event_source_path(&policy);

            println!(
                "monitoring {} v{}",
                session.compiled_graph.name, session.compiled_graph.version
            );
            println!("event_source: {}", event_source_path.display());
            println!("interval_seconds: {}", session.interval_secs);

            for event in monitor(session) {
                println!("{}", pretty_json(&event?)?);
            }

            Ok(ExitCode::SUCCESS)
        }
        Command::Certify {
            policy,
            allow_exponential_consistency,
            claimant,
            outcome,
            evidence,
        } => {
            let context = load_runtime_context_with_options(
                &policy,
                runtime_options(allow_exponential_consistency),
            )?;
            if !context.compiled.is_admissible() {
                println!("REJECTED");
                println!(
                    "rule: {} v{}",
                    context.compiled.name, context.compiled.version
                );
                for violation in context.compiled.violations() {
                    println!("{}", pretty_json(violation)?);
                }
                return Ok(ExitCode::FAILURE);
            }

            let evidence = parse_evidence_entries(&evidence)?;
            let act_description = format!(
                "Governed outcome {outcome} for claimant {} under {}",
                claimant, context.compiled.name
            );
            let certificate: Certificate = certify(
                &CertificationContext {
                    compiled_rule: &context.compiled,
                    rule: &context.parsed.rule,
                    claims: &context.parsed.claims,
                    estate: &context.parsed.estate,
                },
                &act_description,
                &claimant,
                outcome,
                evidence,
            )?;

            println!("{}", pretty_json(&certificate)?);
            Ok(ExitCode::SUCCESS)
        }
        Command::Audit {
            policy,
            allow_exponential_consistency,
            events,
            ledger,
            rule_name,
            rule_version,
            claimant,
            limit,
            verify_chain,
        } => match events {
            Some(events_path) => {
                if verify_chain {
                    return Err(LegitimacyError::invalid_input(
                        "--verify-chain is only supported for ledger audits without --events",
                    ));
                }
                let policy = policy.ok_or_else(|| {
                    LegitimacyError::invalid_input("audit with --events requires a policy path")
                })?;
                let context = load_runtime_context_with_options(
                    &policy,
                    runtime_options(allow_exponential_consistency),
                )?;
                let report = audit_events(&context, &policy, &events_path)?;
                println!("{}", pretty_json(&report)?);
                Ok(ExitCode::SUCCESS)
            }
            None => {
                let ledger = match ledger {
                    Some(path) => Ledger::open(path)?,
                    None => Ledger::open_default()?,
                };
                let audit = ledger.audit(&LedgerQuery {
                    rule_name,
                    rule_version,
                    claimant_id: claimant,
                    limit,
                })?;
                let chain_verification = if verify_chain {
                    Some(ledger.verify_chain()?)
                } else {
                    None
                };
                println!(
                    "{}",
                    pretty_json(&LedgerAuditOutput {
                        audit,
                        chain_verification: chain_verification.clone(),
                    })?
                );
                if chain_verification.is_some_and(|result| !result.valid) {
                    Ok(ExitCode::FAILURE)
                } else {
                    Ok(ExitCode::SUCCESS)
                }
            }
        },
        Command::Protocol { command } => run_protocol_command(command),
        Command::Corpus { command } => corpus::run(command),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PolicyFormat {
    Rule,
    Graph,
}

fn detect_policy_format(policy: &Path) -> Result<PolicyFormat, LegitimacyError> {
    let context = policy.display().to_string();
    let input = fs::read_to_string(policy).map_err(|source| LegitimacyError::PolicyRead {
        path: context.clone(),
        source,
    })?;
    policy_format_for_input_with_context(&input, context)
}

#[cfg(test)]
fn policy_format_for_input(input: &str) -> Result<PolicyFormat, LegitimacyError> {
    policy_format_for_input_with_context(input, "<inline policy format>")
}

fn policy_format_for_input_with_context(
    input: &str,
    context: impl Into<String>,
) -> Result<PolicyFormat, LegitimacyError> {
    let document: toml::Value =
        toml::from_str(input).map_err(|source| LegitimacyError::PolicyToml {
            context: context.into(),
            source,
        })?;

    Ok(
        if document
            .get("graph")
            .and_then(toml::Value::as_table)
            .is_some()
            || document
                .get("nodes")
                .and_then(toml::Value::as_array)
                .is_some_and(|nodes| nodes.iter().all(toml::Value::is_table))
        {
            PolicyFormat::Graph
        } else {
            PolicyFormat::Rule
        },
    )
}

fn monitor_session_for_policy(
    policy: &Path,
    interval_secs: u64,
    allow_exponential_consistency: bool,
) -> Result<MonitorSession, LegitimacyError> {
    let event_source = GovernanceEventSource::jsonl_file(default_policy_event_source_path(policy))?;

    match detect_policy_format(policy)? {
        PolicyFormat::Rule => {
            let context = load_runtime_context_with_options(
                policy,
                runtime_options(allow_exponential_consistency),
            )?;
            let certificate = legitimacy::compile_with_sacrifices_with_family_and_options(
                &context.parsed.rule,
                &context.parsed.claims,
                &context.parsed.claimants,
                &context.parsed.estate,
                &context.parsed.family,
                runtime_options(allow_exponential_consistency).compile,
            )?;

            Ok(MonitorSession {
                compiled_graph: compiled_graph_from_rule(&context.compiled),
                declared_sacrifices: certificate.sacrifices,
                interval_secs,
                event_source,
            })
        }
        PolicyFormat::Graph => {
            let spec = parse_graph_file(policy)?;
            let graph = spec.try_into_graph(policy.display().to_string())?;
            let claims = synthetic_claims(&graph);
            let estate = legitimacy::Estate::new(1.0, "governance_decision")?;
            let certificate = legitimacy::compile_graph_with_sacrifices(&graph, &claims, &estate)?;
            let compiled_graph = match certificate.compiled {
                CompiledGovernance::Graph(compiled) => compiled,
                CompiledGovernance::Rule(_) => {
                    return Err(LegitimacyError::invalid_input(
                        "graph monitor expected graph compilation metadata",
                    ));
                }
            };

            Ok(MonitorSession {
                compiled_graph,
                declared_sacrifices: certificate.sacrifices,
                interval_secs,
                event_source,
            })
        }
    }
}

fn run_protocol_command(command: ProtocolCommand) -> Result<ExitCode, LegitimacyError> {
    match command {
        ProtocolCommand::Init { policy } => {
            if detect_policy_format(&policy)? != PolicyFormat::Graph {
                return Err(LegitimacyError::invalid_input(
                    "protocol init currently requires a graph policy",
                ));
            }
            let spec = parse_graph_file(&policy)?;
            let graph_name = spec.graph.name.clone();
            let graph_version = spec.graph.version.clone();
            let graph = spec.try_into_graph(policy.display().to_string())?;
            let compiled = compile_protocol(
                legitimacy::protocol::declare_with_metadata(
                    graph,
                    Vec::new(),
                    graph_name,
                    graph_version,
                )
                .map_err(protocol_error_to_verdict)?,
            ) // state transition errors become CLI errors
            .map_err(protocol_error_to_verdict)?;
            println!("{}", pretty_json(&compiled)?);
            Ok(ExitCode::SUCCESS)
        }
        ProtocolCommand::Measure { state } => {
            let state = read_protocol_state(&state, false)?;
            let representative_claims = match &state {
                ProtocolState::Compiled { compiled_graph, .. } => {
                    synthetic_claims(&compiled_graph.graph)
                }
                other => {
                    return Err(LegitimacyError::invalid_input(format!(
                        "protocol measure requires a compiled state, found {}",
                        other.name()
                    )));
                }
            };
            let measured = measure_protocol(state, representative_claims)
                .map_err(protocol_error_to_verdict)?;
            println!("{}", pretty_json(&measured)?);
            Ok(ExitCode::SUCCESS)
        }
        ProtocolCommand::Activate {
            state,
            min_interval_seconds,
            max_interval_seconds,
            seed,
        } => {
            if min_interval_seconds > max_interval_seconds {
                return Err(LegitimacyError::invalid_input(format!(
                    "protocol activate requires min_interval_seconds <= max_interval_seconds, found {min_interval_seconds} > {max_interval_seconds}"
                )));
            }

            let state = read_protocol_state(&state, false)?;
            let live = activate_protocol(
                state,
                legitimacy::protocol::MonitorConfig {
                    min_interval_seconds,
                    max_interval_seconds,
                    seed,
                },
            )
            .map_err(protocol_error_to_verdict)?;
            println!("{}", pretty_json(&live)?);
            Ok(ExitCode::SUCCESS)
        }
        ProtocolCommand::Status { state } => {
            let state = read_protocol_state(&state, false)?;
            print_protocol_status(&state);
            Ok(ExitCode::SUCCESS)
        }
        ProtocolCommand::Audit { state } => match protocol_audit_output(&state) {
            Ok(report) => {
                let certificate_chain_valid = report.certificate_chain_valid;
                println!("{}", pretty_json(&report)?);
                if certificate_chain_valid {
                    Ok(ExitCode::SUCCESS)
                } else {
                    eprintln!(
                        "legitimacy: protocol audit detected tampering: certificate_chain_valid: false"
                    );
                    Ok(ExitCode::from(2))
                }
            }
            Err(error) => {
                eprintln!("legitimacy: protocol audit malformed ledger: {error}");
                Ok(ExitCode::from(3))
            }
        },
    }
}

fn protocol_audit_output(state_path: &Path) -> Result<ProtocolAuditOutput, LegitimacyError> {
    let state = read_protocol_state(state_path, true)?;
    let (ledger, latest_drift) = protocol_ledger_view(&state)?;

    Ok(ProtocolAuditOutput {
        state: state.name().to_string(),
        certificates: ledger.certificates.len(),
        drift_alerts: ledger.drift_alerts.len(),
        certificate_chain_valid: verify_protocol_ledger(&ledger)?,
        latest_drift,
    })
}

fn read_protocol_state(
    path: &Path,
    allow_tampered_ledger: bool,
) -> Result<ProtocolState, LegitimacyError> {
    let input = fs::read_to_string(path).map_err(|source| LegitimacyError::Io {
        context: format!("reading protocol state '{}'", path.display()),
        source,
    })?;
    let state: ProtocolState =
        serde_json::from_str(&input).map_err(|source| LegitimacyError::Json {
            context: format!("protocol state '{}'", path.display()),
            source,
        })?;
    let validation = if allow_tampered_ledger {
        state.validate_for_audit()
    } else {
        state.validate()
    };
    validation.map_err(|error| {
        LegitimacyError::invalid_input(format!("protocol state '{}': {error}", path.display()))
    })?;
    Ok(state)
}

fn parse_evidence_entries(entries: &[String]) -> Result<BTreeMap<String, String>, LegitimacyError> {
    let mut evidence = BTreeMap::new();

    for entry in entries {
        let (key, value) = entry.split_once('=').ok_or_else(|| {
            LegitimacyError::invalid_input(format!(
                "invalid evidence entry '{entry}'; expected key=value"
            ))
        })?;
        if key.trim().is_empty() {
            return Err(LegitimacyError::invalid_input(format!(
                "invalid evidence entry '{entry}'; key must not be empty"
            )));
        }
        evidence.insert(key.trim().to_string(), value.to_string());
    }

    Ok(evidence)
}

fn audit_events(
    context: &RuntimeContext,
    policy: &Path,
    events_path: &Path,
) -> Result<ComplianceReport, LegitimacyError> {
    let file = File::open(events_path).map_err(|source| LegitimacyError::Io {
        context: format!("events file '{}'", events_path.display()),
        source,
    })?;
    let reader = BufReader::new(file);
    let mut results = Vec::new();
    let admissible = context.compiled.is_admissible();

    for (index, line) in reader.lines().enumerate() {
        let line_number = index + 1;
        let line = line.map_err(|source| LegitimacyError::Io {
            context: format!("line {line_number} from '{}'", events_path.display()),
            source,
        })?;
        if line.trim().is_empty() {
            continue;
        }

        let event: AuditEvent =
            serde_json::from_str(&line).map_err(|source| LegitimacyError::Json {
                context: format!("line {line_number} of '{}'", events_path.display()),
                source,
            })?;

        let result = if admissible {
            let act_description = event.act_description.clone().unwrap_or_else(|| {
                format!(
                    "Audit event {} for claimant {}",
                    event
                        .event_id
                        .clone()
                        .unwrap_or_else(|| format!("line-{line_number}")),
                    event.claimant_id
                )
            });
            match certify(
                &CertificationContext {
                    compiled_rule: &context.compiled,
                    rule: &context.parsed.rule,
                    claims: &context.parsed.claims,
                    estate: &context.parsed.estate,
                },
                &act_description,
                &event.claimant_id,
                event.outcome,
                event.evidence.clone(),
            ) {
                Ok(certificate) => AuditResult {
                    line: line_number,
                    event_id: event.event_id,
                    claimant_id: event.claimant_id,
                    outcome: event.outcome,
                    status: AuditStatus::Certified,
                    reason: None,
                    certificate: Some(certificate),
                },
                Err(error) => match audit_event_rejection_reason(&error) {
                    Some(reason) => AuditResult {
                        line: line_number,
                        event_id: event.event_id,
                        claimant_id: event.claimant_id,
                        outcome: event.outcome,
                        status: AuditStatus::Rejected,
                        reason: Some(reason),
                        certificate: None,
                    },
                    None => return Err(error),
                },
            }
        } else {
            AuditResult {
                line: line_number,
                event_id: event.event_id,
                claimant_id: event.claimant_id,
                outcome: event.outcome,
                status: AuditStatus::Rejected,
                reason: Some(format!(
                    "rule '{}' v{} is not admissible",
                    context.compiled.name, context.compiled.version
                )),
                certificate: None,
            }
        };

        results.push(result);
    }

    let certified = results
        .iter()
        .filter(|result| matches!(result.status, AuditStatus::Certified))
        .count();
    let rejected = results.len().saturating_sub(certified);
    let compile_violations = context
        .compiled
        .violations()
        .into_iter()
        .map(|violation| violation.description.clone())
        .collect();

    Ok(ComplianceReport {
        policy_path: policy.display().to_string(),
        rule_name: context.compiled.name.clone(),
        rule_version: context.compiled.version.clone(),
        admissible,
        events_total: results.len(),
        certified,
        rejected,
        compile_violations,
        results,
    })
}

fn audit_event_rejection_reason(error: &LegitimacyError) -> Option<String> {
    match error {
        LegitimacyError::RuleNotAdmissible { .. }
        | LegitimacyError::CertificationRuleMismatch { .. }
        | LegitimacyError::CertifiedOutcomeMismatch { .. }
        | LegitimacyError::MissingAllocationShare { .. } => Some(error.to_string()),
        _ => None,
    }
}
