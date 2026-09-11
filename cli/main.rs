mod audit_graph;
mod commands;
mod corpus;
mod input;
mod protocol_support;
mod reporting;
#[cfg(test)]
mod tests;
mod trajectory;
mod trajectory_composition;
mod trajectory_replay;
mod witness;
mod workflow;
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
#[cfg(test)]
use workflow::policy_format_for_input;
use workflow::{
    PolicyFormat, audit_events, consistency_options, detect_policy_format,
    monitor_session_for_policy, parse_evidence_entries, run_protocol_command, runtime_options,
};

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

fn run() -> Result<ExitCode, LegitimacyError> {
    let mut arguments = std::env::args_os().skip(1);
    let first = arguments.next();
    let second = arguments.next();
    let protected_output_attempt =
        first.as_deref().is_some_and(|argument| {
            matches!(
                argument.to_str(),
                Some(
                    "adapt-codex-exec-v0"
                        | "canonicalize-trajectory-v0"
                        | "build-trajectory-replay-candidate-v0"
                        | "issue-trajectory-replay-authority-receipt-v0"
                        | "verify-trajectory-replay-v0"
                        | "evaluate-codex-exec-composition-v0"
                )
            )
        }) || (first.as_deref().is_some_and(|argument| argument == "help")
            && second.as_deref().is_some_and(|argument| {
                matches!(
                    argument.to_str(),
                    Some(
                        "adapt-codex-exec-v0"
                            | "canonicalize-trajectory-v0"
                            | "build-trajectory-replay-candidate-v0"
                            | "issue-trajectory-replay-authority-receipt-v0"
                            | "verify-trajectory-replay-v0"
                            | "evaluate-codex-exec-composition-v0"
                    )
                )
            }));
    let cli = match Cli::try_parse() {
        Ok(cli) => cli,
        Err(error)
            if matches!(
                error.kind(),
                clap::error::ErrorKind::DisplayHelp | clap::error::ErrorKind::DisplayVersion
            ) =>
        {
            error
                .print()
                .map_err(|_| LegitimacyError::invalid_input("cli-output"))?;
            return Ok(ExitCode::SUCCESS);
        }
        Err(_) if protected_output_attempt => {
            eprintln!("legitimacy: cli-arguments");
            return Ok(ExitCode::from(2));
        }
        Err(error) => {
            error
                .print()
                .map_err(|_| LegitimacyError::invalid_input("cli-output"))?;
            return Ok(ExitCode::from(2));
        }
    };

    let Some(command) = cli.command else {
        return Err(LegitimacyError::invalid_input("missing subcommand"));
    };
    if matches!(
        &command,
        Command::AdaptCodexExecV0 {
            output_type: trajectory::CodexExecOutputTypeV0::Private,
            private_lineage_output: Some(_),
            ..
        }
    ) {
        eprintln!("legitimacy: cli-arguments");
        return Ok(ExitCode::from(2));
    }

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
        Command::AdaptCodexExecV0 {
            raw_stdout_jsonl,
            authority_receipt,
            trusted_context,
            output_type,
            output,
            private_lineage_output,
        } => {
            trajectory::run(
                &raw_stdout_jsonl,
                &authority_receipt,
                &trusted_context,
                output_type,
                &output,
                private_lineage_output.as_deref(),
            )
            .map_err(|error| LegitimacyError::invalid_input(error.code().as_str()))?;
            Ok(ExitCode::SUCCESS)
        }
        Command::CanonicalizeTrajectoryV0 { inputs, output } => {
            trajectory_replay::canonicalize(&inputs, &output)
                .map_err(LegitimacyError::invalid_input)?;
            Ok(ExitCode::SUCCESS)
        }
        Command::BuildTrajectoryReplayCandidateV0 { inputs, output } => {
            trajectory_replay::build_candidate(&inputs, &output)
                .map_err(LegitimacyError::invalid_input)?;
            Ok(ExitCode::SUCCESS)
        }
        Command::IssueTrajectoryReplayAuthorityReceiptV0 {
            inputs,
            authority_private_key,
            issuer,
            key_id,
            authority_epoch,
            output,
        } => {
            trajectory_replay::issue_authority_receipt(
                &inputs,
                &authority_private_key,
                &issuer,
                &key_id,
                authority_epoch,
                &output,
            )
            .map_err(LegitimacyError::invalid_input)?;
            Ok(ExitCode::SUCCESS)
        }
        Command::VerifyTrajectoryReplayV0 {
            inputs,
            replay,
            authority_receipt,
            authority_trust_policy,
            output,
        } => {
            trajectory_replay::verify(
                &inputs,
                &replay,
                &authority_receipt,
                &authority_trust_policy,
                &output,
            )
            .map_err(LegitimacyError::invalid_input)?;
            Ok(ExitCode::SUCCESS)
        }
        Command::EvaluateCodexExecCompositionV0 {
            raw_stdout_jsonl,
            input_authority_receipt,
            trusted_adaptation_context,
            shareable_sanitized_bundle,
            private_lineage_sidecar,
            replay_candidate,
            replay_authority_receipt,
            replay_authority_trust_policy,
            composition_policy,
            output,
            trace_output,
            canonical_trace_output,
            output_set,
        } => {
            trajectory_composition::evaluate(
                &trajectory_composition::CodexExecCompositionInputsV0 {
                    raw_stdout_jsonl: &raw_stdout_jsonl,
                    input_authority_receipt: input_authority_receipt.as_deref(),
                    trusted_adaptation_context: trusted_adaptation_context.as_deref(),
                    shareable_sanitized_bundle: shareable_sanitized_bundle.as_deref(),
                    private_lineage_sidecar: private_lineage_sidecar.as_deref(),
                    replay_candidate: &replay_candidate,
                    replay_authority_receipt: &replay_authority_receipt,
                    replay_authority_trust_policy: &replay_authority_trust_policy,
                    composition_policy: &composition_policy,
                },
                &trajectory_composition::CodexExecCompositionOutputsV0 {
                    result: output.as_deref(),
                    trace: trace_output.as_deref(),
                    canonical_trace: canonical_trace_output.as_deref(),
                    output_set: output_set.as_deref(),
                },
            )
            .map_err(LegitimacyError::invalid_input)?;
            Ok(ExitCode::SUCCESS)
        }
    }
}
