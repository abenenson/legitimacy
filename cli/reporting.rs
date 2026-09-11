use serde::Serialize;

use legitimacy::{
    CompiledGovernance, CompiledRule, DeclaredSacrificesCertificate, GovernanceGraph,
    LegitimacyError, StrategyproofnessVerdict, Verdict, detect_cycles,
    extract::{
        ExtractionAxiomResult, ExtractionCycleFinding, ExtractionParadoxResult,
        GovernanceExtractionArtifacts, RecognitionConfidence,
    },
    paradox::ParadoxViolation,
    policy::GraphPolicySpec,
};

const SUPERVISORY_ALGEBRA_SUMMARY: &str =
    "{pause, deny, sandbox, degrade, rollback, reroute, stop}";

pub fn print_extraction_artifacts_report(
    artifacts: &GovernanceExtractionArtifacts,
) -> Result<(), LegitimacyError> {
    println!("EXTRACTION ARTIFACTS");
    println!("source: {}", artifacts.source_dir);
    println!("nodes found: {}", artifacts.graph.nodes.len());
    println!("edges found: {}", artifacts.graph.edges.len());
    println!(
        "coverage: {} parsed / {} discovered ({} skipped, {} errored)",
        artifacts.coverage.files_parsed,
        artifacts.coverage.files_discovered,
        artifacts.coverage.files_skipped,
        artifacts.coverage.files_errored
    );
    println!(
        "boundary-relative compositional safety: {}",
        artifacts.boundary_causal_safety.summary()
    );
    if artifacts.review_overlay.is_some() {
        println!("review overlay: applied");
    }

    if !artifacts.recognized_nodes.is_empty() {
        println!();
        println!("RECOGNIZED NODES");
        for node in &artifacts.recognized_nodes {
            let confidence = match node.confidence {
                RecognitionConfidence::Low => "low",
                RecognitionConfidence::Medium => "medium",
                RecognitionConfidence::High => "high",
            };
            println!(
                "- {} [{}|{:?}] {}:{}-{}",
                node.node_id,
                confidence,
                node.tier,
                node.relative_path,
                node.line_start,
                node.line_end
            );
        }
    }

    if !artifacts.resolution_issues.is_empty() {
        println!();
        println!("RESOLUTION ISSUES");
        for issue in &artifacts.resolution_issues {
            println!(
                "- {} -> {} ({:?}{})",
                issue.caller,
                issue.target_symbol,
                issue.kind,
                if issue.candidates.is_empty() {
                    String::new()
                } else {
                    format!(": {}", issue.candidates.join(", "))
                }
            );
        }
    }

    Ok(())
}

pub fn print_compile_report(compiled: &CompiledRule) -> Result<(), LegitimacyError> {
    if compiled.is_admissible() {
        println!("ADMISSIBLE");
    } else {
        println!("REJECTED");
    }
    println!("rule: {} v{}", compiled.name, compiled.version);
    println!("family: {}", compiled.family_description);
    match &compiled.strategyproofness {
        StrategyproofnessVerdict::Strategyproof => {
            println!("strategyproofness: strategyproof");
        }
        StrategyproofnessVerdict::Manipulable {
            claimant,
            true_strength,
            reported,
            true_alloc,
            manipulated_alloc,
        } => {
            println!("strategyproofness: manipulable");
            println!(
                "manipulation witness: claimant={claimant} true_strength={true_strength} reported={reported} true_alloc={true_alloc} manipulated_alloc={manipulated_alloc}"
            );
        }
    }

    for verdict in &compiled.axiom_verdicts {
        match verdict {
            Verdict::Admissible {
                axiom,
                perturbations_tested,
            } => {
                println!("{axiom}: passed ({perturbations_tested} perturbations tested)");
            }
            Verdict::Rejected {
                axiom,
                counterexample,
            } => {
                println!("{axiom}: rejected");
                println!("{}", pretty_json(counterexample)?);
            }
        }
    }

    Ok(())
}

pub fn print_graph_compile_report(
    spec: &GraphPolicySpec,
    graph: &GovernanceGraph,
) -> Result<(), LegitimacyError> {
    let cycles = detect_cycles(graph)?;

    println!("GRAPH OK");
    println!("graph: {} v{}", spec.graph.name, spec.graph.version);
    println!("nodes: {}", graph.nodes.len());
    println!("edges: {}", graph.edges.len());
    println!("cycles: {}", cycles.len());

    Ok(())
}

pub fn print_sacrifice_report(certificate: &DeclaredSacrificesCertificate) {
    match &certificate.compiled {
        CompiledGovernance::Rule(compiled) => {
            println!("rule: {} v{}", compiled.name, compiled.version);
        }
        CompiledGovernance::Graph(compiled) => {
            println!("graph: {} v{}", compiled.name, compiled.version);
        }
    }

    if certificate.sacrifices.is_empty() {
        println!("declared_sacrifices: none");
        return;
    }

    println!("declared_sacrifices:");
    for sacrifice in &certificate.sacrifices {
        println!(
            "{}: impact_bound={:.4}",
            sacrifice.sacrificed_property.as_str(),
            sacrifice.impact_bound
        );
    }
}

pub fn print_paradox_report(
    compiled: &CompiledRule,
    violations: &[ParadoxViolation],
) -> Result<(), LegitimacyError> {
    if violations.is_empty() {
        println!("NO PARADOX VIOLATIONS");
    } else {
        println!("PARADOX VIOLATIONS");
    }
    println!("rule: {} v{}", compiled.name, compiled.version);

    for violation in violations {
        println!("{}", pretty_json(violation)?);
    }

    Ok(())
}

pub fn print_extraction_report(
    report: &legitimacy::GovernanceExtractionReport,
) -> Result<(), LegitimacyError> {
    let artifacts = &report.artifacts;
    let audit = &report.audit;
    println!("EXTRACTION REPORT");
    println!("source: {}", artifacts.source_dir);
    println!("nodes found: {}", artifacts.graph.nodes.len());
    println!("edges found: {}", artifacts.graph.edges.len());
    println!("cycles detected: {}", audit.cycles.len());
    println!(
        "claim corpus: {:?} ({} claims)",
        audit.corpus_provenance,
        audit.claims.len()
    );
    println!(
        "coverage: {} parsed / {} discovered ({} skipped, {} errored)",
        artifacts.coverage.files_parsed,
        artifacts.coverage.files_discovered,
        artifacts.coverage.files_skipped,
        artifacts.coverage.files_errored
    );
    println!("resolution issues: {}", artifacts.resolution_issues.len());
    if artifacts.review_overlay.is_some() {
        println!("review overlay: applied");
    }

    // Cycle findings
    if !audit.cycles.is_empty() {
        println!();
        println!("CYCLE FINDINGS");
        for finding in &audit.cycles {
            println!("- {}", format_cycle_finding(finding));
        }
    }

    if !artifacts.recognized_nodes.is_empty() {
        println!();
        println!("RECOGNIZED NODES");
        for node in &artifacts.recognized_nodes {
            println!(
                "- {} [{}|{:?}] {}:{}-{}",
                node.node_id,
                match node.confidence {
                    RecognitionConfidence::Low => "low",
                    RecognitionConfidence::Medium => "medium",
                    RecognitionConfidence::High => "high",
                },
                node.tier,
                node.relative_path,
                node.line_start,
                node.line_end
            );
        }
    }

    if !artifacts.resolution_issues.is_empty() {
        println!();
        println!("RESOLUTION ISSUES");
        for issue in &artifacts.resolution_issues {
            println!(
                "- {} -> {} ({:?}{})",
                issue.caller,
                issue.target_symbol,
                issue.kind,
                if issue.candidates.is_empty() {
                    String::new()
                } else {
                    format!(": {}", issue.candidates.join(", "))
                }
            );
        }
    }

    // Axiom status
    println!();
    println!("AXIOM STATUS");
    for line in axiom_status_lines(report)? {
        println!("- {line}");
    }

    // Diagnostic checks
    println!();
    println!("DIAGNOSTIC CHECKS");
    for result in &audit.axiom_results {
        println!("- {}", format_diagnostic_result(result)?);
    }

    // Paradox suite
    println!();
    println!("PARADOX SUITE");
    for result in &audit.paradox_results {
        println!("- {}", format_paradox_result(result));
    }

    // Spectral analysis
    if let Some(spectral) = &audit.spectral {
        println!();
        println!("SPECTRAL ANALYSIS");
        if spectral.node_count == 0 {
            println!("- empty graph (no nodes)");
        } else {
            println!(
                "- graph connectivity: {}",
                if spectral.is_connected {
                    "connected"
                } else {
                    "DISCONNECTED"
                }
            );
            println!("- connected components: {}", spectral.connected_components);
            if spectral.node_count > 1 {
                println!("- spectral gap (lambda_2): {:.3}", spectral.lambda_2);
            } else {
                println!("- spectral gap (lambda_2): N/A");
            }
            println!("- max degree: {}", spectral.max_degree);
            println!("- signal range: {:.2}", spectral.signal_range);
            match &spectral.cv_exact {
                Some(cv) => println!("- cv (exact): {cv}"),
                None => println!("- cv (exact): N/A"),
            }
            match &spectral.c_star {
                Some(c_star) => {
                    println!("- C*(δ={:.3}): {c_star}", spectral.c_star_delta);
                }
                None => println!("- C*(δ={:.3}): N/A", spectral.c_star_delta),
            }
            if let Some(trajectory) = &spectral.rg_trajectory {
                let cv_values = trajectory
                    .iter()
                    .map(|(cv, _)| cv.as_str())
                    .collect::<Vec<_>>()
                    .join(" -> ");
                let c_star_values = trajectory
                    .iter()
                    .map(|(_, c_star)| c_star.as_str())
                    .collect::<Vec<_>>()
                    .join(" -> ");
                println!("- RG trajectory (k=1..3 cv): {cv_values}");
                println!("- RG trajectory (k=1..3 C*): {c_star_values}");
            } else {
                println!("- RG trajectory (k=1..3 cv): N/A");
                println!("- RG trajectory (k=1..3 C*): N/A");
            }
            match spectral.swc {
                Some(swc) => println!(
                    "- spectral well-connected (θ=17/20): {}",
                    if swc { "yes" } else { "no" }
                ),
                None => println!("- spectral well-connected (θ=17/20): N/A"),
            }
            match spectral.capacity {
                Some(capacity) => println!("- capacity bound: {:.3}", capacity),
                None => println!("- capacity bound: N/A"),
            }
            match spectral.capacity_saturated {
                Some(saturated) => println!(
                    "- capacity saturated at ε=0.100: {}",
                    if saturated { "yes" } else { "no" }
                ),
                None => println!("- capacity saturated at ε=0.100: N/A"),
            }
            match spectral.cv_bound {
                Some(cv) => println!("- cv (Cheeger upper bound): {:.3}", cv),
                None => println!("- cv (Cheeger upper bound): N/A"),
            }
            match spectral.localizability_bound {
                Some(loc) => println!("- localizability bound: {:.3}", loc),
                None => println!("- localizability bound: N/A"),
            }
            match spectral.cv_times_localizability {
                Some(product) => {
                    let check = if product >= 0.5 - 1e-9 {
                        "ok"
                    } else {
                        "VIOLATION"
                    };
                    println!("- CV x localizability: {:.3} (>= 0.5 {})", product, check);
                }
                None => println!("- CV x localizability: N/A"),
            }
        }
    }

    // Governance factor exposure
    println!();
    println!("GOVERNANCE FACTOR EXPOSURE");
    println!("{}", audit.factor_exposure.render_text_radar());

    // Protocol state assessment
    println!();
    println!("PROTOCOL STATE ASSESSMENT");
    let assessment = &audit.protocol_assessment;
    println!("- current state: {}", assessment.current_state);
    println!(
        "- governance-observable: {}",
        if assessment.can_declare {
            "YES (graph extracted for principal inspection)"
        } else {
            "NO"
        }
    );
    println!(
        "- can extract-compile: {}",
        if assessment.can_extract_compile {
            "YES (extractor substrate checks completed)"
        } else {
            "NO (requires no cycles, at least one passing axiom, and no rejected axioms)"
        }
    );
    println!(
        "- can measure: {}",
        if assessment.can_measure {
            "YES (spectral analysis computed)"
        } else {
            "NO (spectral analysis unavailable)"
        }
    );
    println!("- supervisory algebra: {}", SUPERVISORY_ALGEBRA_SUMMARY);
    println!(
        "- boundary-relative compositional safety: {}",
        assessment.boundary_causal_safety.summary()
    );
    if !assessment.blocking_issues.is_empty() {
        println!("- blocking for LIVE:");
        for issue in &assessment.blocking_issues {
            println!("  - {}", issue);
        }
    }

    // Recommended sacrifices (brief; details in DIAGNOSTIC CHECKS above)
    if !assessment.recommended_sacrifices.is_empty() {
        println!();
        println!("RECOMMENDED SACRIFICES");
        for (index, sacrifice) in assessment.recommended_sacrifices.iter().enumerate() {
            let impact = sacrifice
                .impact_bound
                .map(|b| format!(" (impact bound: {:.2})", b))
                .unwrap_or_default();
            let brief_reason = brief_sacrifice_reason(&sacrifice.reason);
            let display_property = sacrifice
                .property
                .strip_prefix("graph ")
                .unwrap_or(&sacrifice.property);
            println!(
                "{}. {} -- {}{}",
                index + 1,
                display_property,
                brief_reason,
                impact
            );
        }
    }
    Ok(())
}

fn brief_sacrifice_reason(reason: &str) -> String {
    // Collapse long counterexample descriptions; full detail is in DIAGNOSTIC CHECKS.
    if let Some(idx) = reason.find(":") {
        let head = reason[..idx].trim();
        if head.len() < reason.len() / 2 {
            return format!("{head} (see diagnostic above)");
        }
    }
    if reason.len() > 160 {
        return format!("{}... (see diagnostic above)", &reason[..160]);
    }
    reason.to_string()
}

pub fn print_protocol_status(state: &legitimacy::ProtocolState) {
    println!("state: {}", state.name());
    match state {
        legitimacy::ProtocolState::Undeclared => {}
        legitimacy::ProtocolState::Declared { sacrifices, .. } => {
            println!("declared_sacrifices: {}", sacrifices.len());
        }
        legitimacy::ProtocolState::Compiled {
            compiled_graph,
            sacrifice_certs,
            ..
        } => {
            println!("graph: {} v{}", compiled_graph.name, compiled_graph.version);
            println!("sacrifice_certs: {}", sacrifice_certs.len());
        }
        legitimacy::ProtocolState::Measured {
            compiled_graph,
            risk_report,
            ..
        } => {
            println!("graph: {} v{}", compiled_graph.name, compiled_graph.version);
            println!("spectral_gap: {:.4}", risk_report.spectral_gap);
            println!("cv_bound: {:.4}", risk_report.cv_bound);
        }
        legitimacy::ProtocolState::Live {
            monitor_session,
            ledger,
            ..
        } => {
            println!(
                "graph: {} v{}",
                monitor_session.compiled_graph.name, monitor_session.compiled_graph.version
            );
            println!("interval_seconds: {}", monitor_session.interval_seconds);
            println!("certificates: {}", ledger.certificates.len());
            println!("drift_alerts: {}", ledger.drift_alerts.len());
        }
        legitimacy::ProtocolState::Supervised {
            intervention,
            ledger,
            ..
        } => {
            println!("supervisory_action: {:?}", intervention.action);
            println!("postcondition: {:?}", intervention.postcondition);
            println!("issued_at: {}", intervention.issued_at);
            println!("certificates: {}", ledger.certificates.len());
            println!("drift_alerts: {}", ledger.drift_alerts.len());
        }
        legitimacy::ProtocolState::Drifted {
            drift_report,
            ledger,
            ..
        } => {
            println!("latest_drift: {}", drift_report.alert_type);
            println!("drift_property: {}", drift_report.property.as_str());
            println!("drift_alerts: {}", ledger.drift_alerts.len());
        }
        legitimacy::ProtocolState::Recompiling { sacrifices, .. } => {
            println!("declared_sacrifices: {}", sacrifices.len());
        }
    }
}

pub fn pretty_json(value: &impl Serialize) -> Result<String, LegitimacyError> {
    serde_json::to_string_pretty(value).map_err(|source| LegitimacyError::Serialize {
        context: "CLI output".to_string(),
        source,
    })
}

fn format_cycle_finding(finding: &ExtractionCycleFinding) -> String {
    let cycle = if finding.nodes.is_empty() {
        "(empty cycle)".to_string()
    } else {
        format!(
            "{} -> {}",
            finding.nodes.join(" -> "),
            finding.nodes[0].clone()
        )
    };
    match &finding.verdict {
        Verdict::Admissible {
            perturbations_tested,
            ..
        } => {
            format!("{cycle}: converged ({perturbations_tested} iterations checked)")
        }
        Verdict::Rejected { counterexample, .. } => {
            format!(
                "{cycle}: {} ({})",
                counterexample.violation, counterexample.description
            )
        }
    }
}

fn axiom_status_lines(
    report: &legitimacy::GovernanceExtractionReport,
) -> Result<Vec<String>, LegitimacyError> {
    Ok(vec![
        kernel_axiom_brief(report, "CERTIFIABLE", "graph certifiability")?,
        kernel_axiom_brief(
            report,
            "GOVERNANCE-OBSERVABLE",
            "graph observable determinacy",
        )?,
        kernel_axiom_brief(report, "CORRIGIBLE", "graph corrigibility")?,
        kernel_axiom_brief(report, "COMPOSITIONAL SAFETY", "graph compositional safety")?,
        kernel_axiom_brief(report, "NON-VACUOUS", "graph nonvacuity")?,
    ])
}

fn kernel_axiom_brief(
    report: &legitimacy::GovernanceExtractionReport,
    label: &str,
    axiom: &str,
) -> Result<String, LegitimacyError> {
    let result = report.audit.axiom_results.iter().find(|r| r.axiom == axiom);
    let Some(result) = result else {
        return Ok(format!("{label}: DIAGNOSTIC UNAVAILABLE"));
    };
    if let Some(reason) = &result.skipped_reason {
        return Ok(format!("{label}: SKIPPED ({reason})"));
    }
    match result.verdict.as_ref().ok_or_else(|| {
        LegitimacyError::invalid_input(format!(
            "axiom result for '{}' has neither verdict nor skipped_reason",
            result.axiom
        ))
    })? {
        Verdict::Admissible { .. } => Ok(format!("{label}: SUPPORTED (projection verdict passed)")),
        Verdict::Rejected { counterexample, .. } => Ok(format!(
            "{label}: REJECTED ({})",
            counterexample.description
        )),
    }
}

fn format_diagnostic_result(result: &ExtractionAxiomResult) -> Result<String, LegitimacyError> {
    let diagnostic_name = match result.axiom.as_str() {
        "graph strategyproofness" => {
            "graph strategyproofness (derived via solidarity_monotonicity_imply_strategyproof; empirical monitor)"
        }
        "graph certifiability" => "graph certifiability (implements CERTIFIABLE projection)",
        "graph observable determinacy" => {
            "graph observable determinacy (implements GOVERNANCE-OBSERVABLE projection)"
        }
        "graph corrigibility" => "graph corrigibility (implements CORRIGIBLE projection)",
        "graph compositional safety" => {
            "graph compositional safety (implements COMPOSITIONAL SAFETY projection)"
        }
        "graph nonvacuity" => "graph nonvacuity (implements NON-VACUOUS axiom)",
        _ => result.axiom.as_str(),
    };

    if let Some(reason) = &result.skipped_reason {
        return Ok(format!("{diagnostic_name}: skipped ({reason})"));
    }

    match result.verdict.as_ref().ok_or_else(|| {
        LegitimacyError::invalid_input(format!(
            "axiom result for '{}' has neither verdict nor skipped_reason",
            result.axiom
        ))
    })? {
        Verdict::Admissible {
            perturbations_tested,
            ..
        } => Ok(format!(
            "{diagnostic_name}: passed ({perturbations_tested} perturbations)"
        )),
        Verdict::Rejected { counterexample, .. } => Ok(format!(
            "{diagnostic_name}: REJECTED -- {}",
            counterexample.description
        )),
    }
}

fn format_paradox_result(result: &ExtractionParadoxResult) -> String {
    if let Some(reason) = &result.skipped_reason {
        return format!("{}: skipped ({reason})", result.paradox);
    }

    match &result.violation {
        Some(violation) => format!("{}: detected -- {}", result.paradox, violation.description),
        None => format!("{}: none", result.paradox),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn diagnostic_result_renders_skipped_reason_without_pass_zero() {
        let line = format_diagnostic_result(&ExtractionAxiomResult {
            axiom: "graph observable determinacy".to_string(),
            verdict: None,
            skipped_reason: Some("graph has no branching decision surface".to_string()),
        })
        .unwrap();

        assert!(line.contains("skipped (graph has no branching decision surface)"));
        let stale_pass_zero_label = ["passed", "(0 perturbations)"].join(" ");
        assert!(!line.contains(&stale_pass_zero_label));
    }
}
