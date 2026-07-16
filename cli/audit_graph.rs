use crate::{
    input::{
        ClaimCorpusInputProvenance, load_claim_corpus, load_governance_graph, load_review_overlay,
    },
    reporting::print_extraction_report,
};
use clap::Args;
use legitimacy::{
    BoundaryCausalSafetyAssessment, GovernanceGraph, LegitimacyError,
    analyze_extraction_with_review, audit_extracted_graph_with_review, audit_governance_graph,
    extract::{
        ExtractionCoverageReport, ExtractionOptions, GovernanceExtractionArtifacts,
        spectral::{PaperDiagnostics, paper_diagnostics},
        synthetic_claims,
    },
    policy::parse_graph_file,
    spectral::{self, Rational},
};
use std::{
    path::{Path, PathBuf},
    process::ExitCode,
};

#[derive(Args, Debug)]
pub(crate) struct AuditGraphCommand {
    /// Existing serialized governance graph JSON file.
    #[arg(long)]
    pub(crate) graph: Option<PathBuf>,
    /// Or extract governance artifacts from this source directory first.
    #[arg(long)]
    pub(crate) source_dir: Option<PathBuf>,
    /// JSON or JSONL claim corpus file.
    #[arg(long)]
    pub(crate) claims: Option<PathBuf>,
    /// Audit the graph against the synthetic structural probe corpus.
    #[arg(long, conflicts_with = "claims")]
    pub(crate) claims_synthetic: bool,
    /// Provenance label for the supplied claim corpus.
    #[arg(long, value_enum, default_value = "user-supplied")]
    pub(crate) claims_provenance: ClaimCorpusInputProvenance,
    /// Optional review overlay JSON to promote curated nodes/edges and alias hints.
    #[arg(long)]
    pub(crate) review_overlay: Option<PathBuf>,
    /// Allow partial extraction when sourcing from code.
    #[arg(long)]
    pub(crate) allow_partial: bool,
    /// Add Paper 1 v3 interpretive captions for cv, C*, and SpectralWellConnected.
    #[arg(long)]
    pub(crate) interpret: bool,
    /// Compute `S_delta = lambda_2 x cv` for a graph policy and return exit code 0/2.
    #[arg(long, value_name = "GRAPH.toml")]
    pub(crate) spectral_well_connected: Option<PathBuf>,
    /// Also report the normalized-Laplacian gap `lambda_2(L_tilde)`.
    #[arg(long)]
    pub(crate) normalized_spectral_gap: bool,
    /// Adversary bound delta used when labeling `C*(G, delta)`.
    #[arg(long, default_value_t = 0.1)]
    pub(crate) delta: f64,
}

pub(crate) fn run(command: AuditGraphCommand) -> Result<ExitCode, LegitimacyError> {
    if let Some(path) = command.spectral_well_connected.as_ref() {
        validate_spectral_well_connected_mode(&command)?;
        let (label, graph) = load_graph_policy(path)?;
        let diagnostics = paper_diagnostics(&graph, command.delta)?;
        print_spectral_well_connected_report(
            &label,
            &diagnostics,
            command.interpret,
            command.normalized_spectral_gap,
        );
        return Ok(if diagnostics.spectral_well_connected {
            ExitCode::SUCCESS
        } else {
            ExitCode::from(2)
        });
    }

    if command.claims.is_none() && !command.claims_synthetic {
        return Err(LegitimacyError::invalid_input(
            "audit-graph requires --claims or --claims-synthetic unless --spectral-well-connected is used",
        ));
    }
    let review_overlay = command
        .review_overlay
        .as_ref()
        .map(|path| load_review_overlay(path))
        .transpose()?;
    let report = match (&command.graph, &command.source_dir) {
        (Some(graph_path), None) => {
            let graph = load_governance_graph(graph_path)?;
            let (corpus, corpus_provenance) = if command.claims_synthetic {
                (
                    synthetic_claims(&graph),
                    legitimacy::ClaimCorpusProvenance::SyntheticStructuralProbe,
                )
            } else {
                (
                    load_claim_corpus(command.claims.as_ref().expect("claims presence checked"))?,
                    command.claims_provenance.into(),
                )
            };
            let audit = audit_governance_graph(
                &graph,
                corpus,
                corpus_provenance,
                BoundaryCausalSafetyAssessment::default(),
            )?;
            legitimacy::GovernanceExtractionReport {
                artifacts: GovernanceExtractionArtifacts {
                    source_dir: graph_path.display().to_string(),
                    graph,
                    coverage: ExtractionCoverageReport {
                        files_discovered: 0,
                        files_parsed: 0,
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
                },
                audit,
            }
        }
        (None, Some(source_dir)) => {
            let options = ExtractionOptions {
                allow_partial: command.allow_partial,
                ..ExtractionOptions::default()
            };
            if command.claims_synthetic {
                analyze_extraction_with_review(source_dir, options, review_overlay.as_ref())?
            } else {
                audit_extracted_graph_with_review(
                    source_dir,
                    load_claim_corpus(command.claims.as_ref().expect("claims presence checked"))?,
                    options,
                    command.claims_provenance.into(),
                    review_overlay.as_ref(),
                )?
            }
        }
        _ => {
            return Err(LegitimacyError::invalid_input(
                "audit-graph requires exactly one of --graph or --source-dir",
            ));
        }
    };

    print_extraction_report(&report)?;
    if command.interpret || command.normalized_spectral_gap {
        let diagnostics = paper_diagnostics(&report.artifacts.graph, command.delta)?;
        println!();
        print_paper_diagnostics(
            &diagnostics,
            command.interpret,
            command.normalized_spectral_gap,
        );
    }

    Ok(ExitCode::SUCCESS)
}

fn validate_spectral_well_connected_mode(
    command: &AuditGraphCommand,
) -> Result<(), LegitimacyError> {
    if command.graph.is_some()
        || command.source_dir.is_some()
        || command.claims.is_some()
        || command.claims_synthetic
        || command.review_overlay.is_some()
        || command.allow_partial
    {
        return Err(LegitimacyError::invalid_input(
            "--spectral-well-connected is a standalone audit-graph mode",
        ));
    }

    Ok(())
}

fn load_graph_policy(path: &Path) -> Result<(String, GovernanceGraph), LegitimacyError> {
    let spec = parse_graph_file(path)?;
    let label = format!("{} v{}", spec.graph.name, spec.graph.version);
    let graph = spec.try_into_graph(path.display().to_string())?;
    Ok((label, graph))
}

fn print_spectral_well_connected_report(
    label: &str,
    diagnostics: &PaperDiagnostics,
    interpret: bool,
    include_normalized_gap: bool,
) {
    println!("SPECTRAL WELL CONNECTED");
    println!("graph: {label}");
    print_paper_diagnostics(diagnostics, interpret, include_normalized_gap);
}

fn print_paper_diagnostics(
    diagnostics: &PaperDiagnostics,
    interpret: bool,
    include_normalized_gap: bool,
) {
    println!(
        "probe signal s: ordinal node-id signature 1..{}",
        diagnostics.signal_dimension
    );
    println!(
        "- connected components: {}",
        diagnostics.connected_components
    );
    println!("- cv(G, s): {}", format_rational(diagnostics.cv));
    if interpret {
        println!("  (= Cook's 1977 influence sup-norm over single-node deletion)");
    }
    match diagnostics.c_star {
        Some(c_star) => {
            println!(
                "- C*(G, delta={:.3}): {}",
                diagnostics.delta,
                format_rational(c_star)
            );
            if interpret {
                println!(
                    "  (= inverse Laplace-mechanism noise scale for delta-DP release of gov(s))"
                );
            }
        }
        None => {
            println!("- C*(G, delta={:.3}): N/A", diagnostics.delta);
            if interpret {
                if diagnostics.cv <= Rational::from_integer(0) {
                    println!("  (undefined because the positive-CV hypothesis for C* is not met)");
                } else {
                    println!(
                        "  (undefined because the connected-carrier positive-gap hypothesis for C* is not met)"
                    );
                }
            }
        }
    }
    println!("- lambda_2: {:.6}", diagnostics.lambda_2);
    println!("- S_delta = lambda_2 x cv: {:.6}", diagnostics.s_delta);
    println!(
        "- SpectralWellConnected(G, s): {}",
        diagnostics.spectral_well_connected
    );
    if interpret {
        if diagnostics.connected_components > 1 {
            println!(
                "  (disconnected carrier: lambda_2 is the true second-smallest Laplacian eigenvalue)"
            );
        }
        println!(
            "  (S_delta = lambda_2 x cv; >= 17/20 is cross-scale classifier cut on n=5/7/9/11/13 probe archetypes)"
        );
    }
    if include_normalized_gap {
        println!(
            "- lambda_2(L_tilde): {:.6}",
            diagnostics.normalized_lambda_2
        );
        if interpret {
            println!(
                "  (normalized-Laplacian gap: ordinal MI predictor only, not a basin classifier)"
            );
        }
    }
}

fn format_rational(value: Rational) -> String {
    let exact = if value.denom() == &1 {
        value.numer().to_string()
    } else {
        format!("{}/{}", value.numer(), value.denom())
    };
    format!("{exact} ({:.6})", spectral::ratio_to_f64(value))
}
