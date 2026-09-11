use super::*;

pub(super) fn consistency_options(allow_exponential_consistency: bool) -> FullConsistencyOptions {
    FullConsistencyOptions {
        allow_exponential_consistency,
        ..FullConsistencyOptions::default()
    }
}

pub(super) fn runtime_options(allow_exponential_consistency: bool) -> RuntimeOptions {
    RuntimeOptions {
        compile: CompileOptions {
            consistency: consistency_options(allow_exponential_consistency),
        },
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum PolicyFormat {
    Rule,
    Graph,
}

pub(super) fn detect_policy_format(policy: &Path) -> Result<PolicyFormat, LegitimacyError> {
    let context = policy.display().to_string();
    let input = fs::read_to_string(policy).map_err(|source| LegitimacyError::PolicyRead {
        path: context.clone(),
        source,
    })?;
    policy_format_for_input_with_context(&input, context)
}

#[cfg(test)]
pub(super) fn policy_format_for_input(input: &str) -> Result<PolicyFormat, LegitimacyError> {
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

pub(super) fn monitor_session_for_policy(
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

pub(super) fn run_protocol_command(command: ProtocolCommand) -> Result<ExitCode, LegitimacyError> {
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
            )
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

pub(super) fn parse_evidence_entries(
    entries: &[String],
) -> Result<BTreeMap<String, String>, LegitimacyError> {
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

pub(super) fn audit_events(
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
