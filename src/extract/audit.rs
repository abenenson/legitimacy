//! Audit pipeline for extracted governance graphs.
//!
//! Claim corpus provenance is intentionally hierarchical:
//! automatic extraction evidence is orthogonal to claim-corpus evidence, and
//! explicit corpora are not interchangeable. `SyntheticStructuralProbe` is the
//! weakest tier and exists to stress graph structure without making empirical
//! runtime claims. `Fixture` and `UserSupplied` preserve caller-provided
//! corpora exactly. `ObservedRuntime` records represent real runtime traces,
//! but they may be sparse with respect to the graph's numeric gate fields; the
//! audit layer therefore zero-fills absent numeric metrics so the trace can be
//! evaluated honestly as "field not observed" rather than rejected as malformed
//! schema. `ReviewedReconstruction` remains explicit-corpus evidence, but with
//! human-curated reconstruction semantics rather than direct runtime capture.

use super::{
    ClaimCorpusProvenance, ExtractionOptions, ExtractionReviewOverlay, GovernanceExtractionReport,
};
#[cfg(test)]
use super::{ExtractionCoverageReport, GovernanceExtractionArtifacts};
use crate::{
    Decision, Gate, GovernanceClaim, GovernanceGraph, GovernanceNode, LegitimacyError, Verdict,
    axioms::{
        binary::{BinaryDelta, BinaryShock},
        graph::{
            consistency::check_graph_consistency,
            monotonicity::monotonicity_check_via_polarity_schema,
            solidarity::check_graph_solidarity, strategyproofness::check_graph_strategyproofness,
        },
        kernel::{
            check_graph_certifiability, check_graph_compositional_safety,
            check_graph_corrigibility, check_graph_nonvacuity, check_graph_observable_determinacy,
        },
    },
    extract::{BoundaryCausalSafetyAssessment, GovernanceAuditReport, spectral},
    factor::GovernanceFactorExposure,
    graph::{check_cycle_admissibility, detect_cycles},
    paradox::{
        GraphParadoxViolation, compositional_alabama, feedback_monotonicity, path_dependence,
    },
};
use serde::Serialize;
use spectral::SpectralAnalysis;
use std::{
    collections::{BTreeMap, BTreeSet},
    path::Path,
};

#[derive(Debug, Clone, Serialize, PartialEq)]
pub struct ExtractionCycleFinding {
    pub nodes: Vec<String>,
    pub verdict: Verdict,
}

#[derive(Debug, Clone, Serialize, PartialEq)]
pub struct ExtractionAxiomResult {
    pub axiom: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub verdict: Option<Verdict>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub skipped_reason: Option<String>,
}

#[derive(Debug, Clone, Serialize, PartialEq)]
pub struct ExtractionParadoxResult {
    pub paradox: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub violation: Option<GraphParadoxViolation>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub skipped_reason: Option<String>,
}

/// Assessment of what protocol state this extracted governance system could reach.
#[derive(Debug, Clone, Serialize)]
pub struct ProtocolStateAssessment {
    pub current_state: String,
    pub can_declare: bool,
    pub can_extract_compile: bool,
    pub can_measure: bool,
    pub boundary_causal_safety: BoundaryCausalSafetyAssessment,
    pub blocking_issues: Vec<String>,
    pub recommended_sacrifices: Vec<RecommendedSacrifice>,
}

/// A recommended property sacrifice based on axiom check failures.
#[derive(Debug, Clone, Serialize)]
pub struct RecommendedSacrifice {
    pub property: String,
    pub reason: String,
    pub impact_bound: Option<f64>,
}

pub fn analyze_extraction(
    source_dir: &Path,
) -> Result<GovernanceExtractionReport, LegitimacyError> {
    analyze_extraction_with_review(source_dir, ExtractionOptions::default(), None)
}

pub fn analyze_extraction_with_review(
    source_dir: &Path,
    options: ExtractionOptions,
    review_overlay: Option<&ExtractionReviewOverlay>,
) -> Result<GovernanceExtractionReport, LegitimacyError> {
    let artifacts =
        super::extract_governance_artifacts_with_review(source_dir, options, review_overlay)?;
    let claims = synthetic_claims(&artifacts.graph);
    let audit = audit_governance_graph(
        &artifacts.graph,
        claims,
        ClaimCorpusProvenance::SyntheticStructuralProbe,
        artifacts.boundary_causal_safety.clone(),
    )?;
    Ok(GovernanceExtractionReport { artifacts, audit })
}

pub fn audit_extracted_graph(
    source_dir: &Path,
    claims: Vec<GovernanceClaim>,
    options: ExtractionOptions,
) -> Result<GovernanceExtractionReport, LegitimacyError> {
    audit_extracted_graph_with_review(
        source_dir,
        claims,
        options,
        ClaimCorpusProvenance::UserSupplied,
        None,
    )
}

pub fn audit_extracted_graph_with_review(
    source_dir: &Path,
    claims: Vec<GovernanceClaim>,
    options: ExtractionOptions,
    corpus_provenance: ClaimCorpusProvenance,
    review_overlay: Option<&ExtractionReviewOverlay>,
) -> Result<GovernanceExtractionReport, LegitimacyError> {
    let artifacts =
        super::extract_governance_artifacts_with_review(source_dir, options, review_overlay)?;
    let audit = audit_governance_graph(
        &artifacts.graph,
        claims,
        corpus_provenance,
        artifacts.boundary_causal_safety.clone(),
    )?;
    Ok(GovernanceExtractionReport { artifacts, audit })
}

pub fn audit_governance_graph(
    graph: &GovernanceGraph,
    claims: Vec<GovernanceClaim>,
    corpus_provenance: ClaimCorpusProvenance,
    boundary_causal_safety: BoundaryCausalSafetyAssessment,
) -> Result<GovernanceAuditReport, LegitimacyError> {
    audit_graph_with_boundary(graph, claims, corpus_provenance, boundary_causal_safety)
}

#[cfg(test)]
pub(crate) fn analyze_graph(
    source_dir: &Path,
    graph: GovernanceGraph,
) -> Result<GovernanceExtractionReport, LegitimacyError> {
    let artifacts = GovernanceExtractionArtifacts {
        source_dir: source_dir.display().to_string(),
        graph: graph.clone(),
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
    };
    let claims = synthetic_claims(&graph);
    let audit = audit_graph_with_boundary(
        &graph,
        claims,
        ClaimCorpusProvenance::SyntheticStructuralProbe,
        BoundaryCausalSafetyAssessment::default(),
    )?;
    Ok(GovernanceExtractionReport { artifacts, audit })
}

fn audit_graph_with_boundary(
    graph: &GovernanceGraph,
    claims: Vec<GovernanceClaim>,
    corpus_provenance: ClaimCorpusProvenance,
    boundary_causal_safety: BoundaryCausalSafetyAssessment,
) -> Result<GovernanceAuditReport, LegitimacyError> {
    let claims = normalize_claims_for_graph(graph, claims, &corpus_provenance);
    let cycles = detect_cycles(graph)?;
    let cycle_findings = cycles
        .iter()
        .map(|cycle| {
            let cycle_claims = claims_for_cycle(graph, &claims, cycle);
            Ok(ExtractionCycleFinding {
                nodes: cycle.iter().map(ToString::to_string).collect(),
                verdict: check_cycle_admissibility(graph, cycle, &cycle_claims)?,
            })
        })
        .collect::<Result<Vec<_>, LegitimacyError>>()?;
    let axiom_results = run_graph_axiom_checks(graph, &claims, !cycles.is_empty())?;
    let paradox_claims = if cycles.is_empty() {
        claims.clone()
    } else {
        claims_for_cycles(graph, &claims, &cycles)
    };
    let paradox_results = run_graph_paradox_suite(graph, &paradox_claims, !cycles.is_empty())?;
    let spectral = Some(spectral::spectral_analysis(graph, &claims));
    let factor_exposure = graph_factor_exposure(&axiom_results);
    let protocol_assessment = assess_protocol_state(
        &axiom_results,
        spectral.as_ref(),
        !cycles.is_empty(),
        boundary_causal_safety,
    );

    Ok(GovernanceAuditReport {
        corpus_provenance,
        claims,
        cycles: cycle_findings,
        axiom_results,
        paradox_results,
        spectral,
        factor_exposure,
        protocol_assessment,
    })
}

fn normalize_claims_for_graph(
    graph: &GovernanceGraph,
    claims: Vec<GovernanceClaim>,
    corpus_provenance: &ClaimCorpusProvenance,
) -> Vec<GovernanceClaim> {
    if !matches!(corpus_provenance, ClaimCorpusProvenance::ObservedRuntime) {
        return claims;
    }

    let numeric_fields = graph_numeric_fields(graph);
    claims
        .into_iter()
        .map(|mut claim| {
            for field in &numeric_fields {
                claim.metrics.entry(field.clone()).or_insert(0.0);
            }
            claim
        })
        .collect()
}

fn graph_numeric_fields(graph: &GovernanceGraph) -> BTreeSet<String> {
    let mut fields = BTreeSet::new();
    for node in graph.nodes.values() {
        match node {
            GovernanceNode::Binary { gates, .. } => {
                for gate in gates {
                    match gate {
                        Gate::ThresholdGate { field, .. } | Gate::PeerRelative { field, .. } => {
                            if field != "strength" {
                                fields.insert(field.clone());
                            }
                        }
                        Gate::PrefixMatch { .. }
                        | Gate::ExactMatch { .. }
                        | Gate::ContentMatch { .. } => {}
                    }
                }
            }
            GovernanceNode::Threshold { field, .. } if field != "strength" => {
                fields.insert(field.clone());
            }
            GovernanceNode::Threshold { .. } | GovernanceNode::Proportional { .. } => {}
        }
    }
    fields
}

fn run_graph_axiom_checks(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
    has_cycles: bool,
) -> Result<Vec<ExtractionAxiomResult>, LegitimacyError> {
    let cycles = if has_cycles {
        detect_cycles(graph)?
    } else {
        Vec::new()
    };
    if has_cycles {
        let reason =
            "skipped because the extracted graph contains cycles; see cycle findings".to_string();
        let mut results = vec![
            skipped_axiom("graph consistency", &reason),
            skipped_axiom("graph solidarity", &reason),
            skipped_axiom("graph monotonicity", &reason),
            skipped_axiom("graph strategyproofness", &reason),
            skipped_axiom("graph certifiability", &reason),
            skipped_axiom("graph observable determinacy", &reason),
            skipped_axiom("graph corrigibility", &reason),
            skipped_axiom("graph compositional safety", &reason),
        ];
        results.push(ExtractionAxiomResult {
            axiom: "graph nonvacuity".to_string(),
            ..kernel_axiom_result(check_graph_nonvacuity(graph, claims, &cycles)?)
        });
        return Ok(results);
    }

    let certifiability = kernel_axiom_result(check_graph_certifiability(graph, claims)?);
    let observable = kernel_axiom_result(check_graph_observable_determinacy(graph, claims)?);
    let corrigibility = kernel_axiom_result(check_graph_corrigibility(graph, claims)?);
    let compositional_safety =
        kernel_axiom_result(check_graph_compositional_safety(graph, claims)?);
    let nonvacuity = kernel_axiom_result(check_graph_nonvacuity(graph, claims, &cycles)?);

    let fields = graph_fields(claims);
    let shocks = graph_shocks(&fields);
    let deltas = graph_deltas(&fields);

    Ok(vec![
        ExtractionAxiomResult {
            axiom: "graph consistency".to_string(),
            verdict: Some(check_graph_consistency(graph, claims)?),
            skipped_reason: None,
        },
        ExtractionAxiomResult {
            axiom: "graph solidarity".to_string(),
            verdict: Some(check_graph_solidarity(graph, claims, &shocks)?),
            skipped_reason: None,
        },
        ExtractionAxiomResult {
            axiom: "graph monotonicity".to_string(),
            verdict: Some(monotonicity_check_via_polarity_schema(
                graph,
                claims,
                &deltas,
                &Default::default(),
            )?),
            skipped_reason: None,
        },
        ExtractionAxiomResult {
            axiom: "graph strategyproofness".to_string(),
            verdict: Some(check_graph_strategyproofness(graph, claims)?),
            skipped_reason: None,
        },
        certifiability,
        observable,
        corrigibility,
        compositional_safety,
        nonvacuity,
    ])
}

fn run_graph_paradox_suite(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
    has_cycles: bool,
) -> Result<Vec<ExtractionParadoxResult>, LegitimacyError> {
    let mut results = Vec::with_capacity(3);

    if has_cycles {
        let reason = "skipped because compositional Alabama requires an acyclic baseline traversal; cycles are reported separately".to_string();
        results.push(ExtractionParadoxResult {
            paradox: "compositional Alabama".to_string(),
            violation: None,
            skipped_reason: Some(reason),
        });
    } else {
        results.push(ExtractionParadoxResult {
            paradox: "compositional Alabama".to_string(),
            violation: compositional_alabama(graph, claims)?,
            skipped_reason: None,
        });
    }

    results.push(ExtractionParadoxResult {
        paradox: "feedback monotonicity".to_string(),
        violation: feedback_monotonicity(graph, claims)?,
        skipped_reason: None,
    });

    if has_cycles {
        let reason = "skipped because path dependence is defined over alternate DAG evaluation orders; cycles are reported separately".to_string();
        results.push(ExtractionParadoxResult {
            paradox: "path dependence".to_string(),
            violation: None,
            skipped_reason: Some(reason),
        });
    } else {
        results.push(ExtractionParadoxResult {
            paradox: "path dependence".to_string(),
            violation: path_dependence(graph, claims)?,
            skipped_reason: None,
        });
    }

    Ok(results)
}

fn graph_factor_exposure(axiom_results: &[ExtractionAxiomResult]) -> GovernanceFactorExposure {
    let lookup = |name: &str| -> f64 {
        axiom_results
            .iter()
            .find(|result| result.axiom == name)
            .map(|result| {
                if result.skipped_reason.is_some() {
                    0.5
                } else {
                    match &result.verdict {
                        Some(Verdict::Rejected { .. }) => 1.0,
                        Some(Verdict::Admissible { .. }) => 0.0,
                        None => 0.5,
                    }
                }
            })
            .unwrap_or(0.5)
    };

    GovernanceFactorExposure {
        consistency: lookup("graph consistency"),
        solidarity: lookup("graph solidarity"),
        monotonicity: lookup("graph monotonicity"),
        strategyproofness: lookup("graph strategyproofness"),
        nonvacuity: lookup("graph nonvacuity"),
    }
}

fn assess_protocol_state(
    axiom_results: &[ExtractionAxiomResult],
    spectral: Option<&SpectralAnalysis>,
    has_cycles: bool,
    boundary_causal_safety: BoundaryCausalSafetyAssessment,
) -> ProtocolStateAssessment {
    let can_declare = true;
    let can_extract_compile = protocol_can_extract_compile(axiom_results, has_cycles);
    let can_measure = spectral.is_some_and(|analysis| analysis.spectral_gap.is_some());

    let mut blocking_issues = Vec::new();
    if has_cycles {
        blocking_issues.push("graph contains cycles; axiom checks were skipped".to_string());
    }
    let rejected_count = axiom_results
        .iter()
        .filter(|result| matches!(&result.verdict, Some(Verdict::Rejected { .. })))
        .count();
    if rejected_count > 0 {
        blocking_issues.push(format!(
            "{rejected_count} axiom check(s) rejected; sacrifices required before promotion"
        ));
    }
    if !can_measure {
        blocking_issues.push(
            "spectral analysis could not compute algebraic connectivity (disconnected graph or single node)".to_string(),
        );
    }
    if let Some(blocker) = boundary_causal_safety.live_blocker() {
        blocking_issues.push(blocker.to_string());
    }
    blocking_issues.push("no monitoring infrastructure detected".to_string());

    let mut recommended_sacrifices = Vec::new();
    for result in axiom_results {
        if let Some(Verdict::Rejected { counterexample, .. }) = &result.verdict {
            recommended_sacrifices.push(RecommendedSacrifice {
                property: result.axiom.clone(),
                reason: counterexample.description.clone(),
                impact_bound: None,
            });
        }
    }

    ProtocolStateAssessment {
        current_state: "UNDECLARED".to_string(),
        can_declare,
        can_extract_compile,
        can_measure,
        boundary_causal_safety,
        blocking_issues,
        recommended_sacrifices,
    }
}

fn protocol_can_extract_compile(axiom_results: &[ExtractionAxiomResult], has_cycles: bool) -> bool {
    let any_pass = axiom_results
        .iter()
        .any(|result| matches!(result.verdict, Some(Verdict::Admissible { .. })));
    let any_reject = axiom_results
        .iter()
        .any(|result| matches!(result.verdict, Some(Verdict::Rejected { .. })));

    !has_cycles && any_pass && !any_reject
}

fn skipped_axiom(name: &str, reason: &str) -> ExtractionAxiomResult {
    ExtractionAxiomResult {
        axiom: name.to_string(),
        verdict: None,
        skipped_reason: Some(reason.to_string()),
    }
}

pub(crate) fn kernel_axiom_result(
    verdict: crate::axioms::kernel::AxiomVerdict,
) -> ExtractionAxiomResult {
    match verdict {
        crate::axioms::kernel::AxiomVerdict::Skipped { axiom, reason } => ExtractionAxiomResult {
            axiom: axiom.graph_axiom_name().to_string(),
            verdict: None,
            skipped_reason: Some(reason),
        },
        other => ExtractionAxiomResult {
            axiom: match &other {
                crate::axioms::kernel::AxiomVerdict::Pass { axiom, .. }
                | crate::axioms::kernel::AxiomVerdict::Fail { axiom, .. } => {
                    axiom.graph_axiom_name().to_string()
                }
                // SAFETY: the outer match handles Skipped before binding this
                // arm as `other`, so `other` cannot be Skipped here.
                crate::axioms::kernel::AxiomVerdict::Skipped { .. } => unreachable!(),
            },
            verdict: Some(
                crate::Verdict::try_from(other).expect("non-skipped kernel verdict must convert"),
            ),
            skipped_reason: None,
        },
    }
}

fn claims_for_cycle(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
    cycle: &[crate::NodeId],
) -> Vec<GovernanceClaim> {
    if claims.is_empty() {
        synthetic_claims_for_cycle(graph, cycle)
    } else {
        claims.to_vec()
    }
}

fn claims_for_cycles(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
    cycles: &[Vec<crate::NodeId>],
) -> Vec<GovernanceClaim> {
    if claims.is_empty() {
        synthetic_claims_for_cycles(graph, cycles)
    } else {
        claims.to_vec()
    }
}

pub fn synthetic_claims(graph: &GovernanceGraph) -> Vec<GovernanceClaim> {
    synthetic_claims_for_nodes(graph, graph.nodes.keys().cloned().collect())
}

pub(crate) fn synthetic_claims_for_cycle(
    graph: &GovernanceGraph,
    cycle: &[crate::NodeId],
) -> Vec<GovernanceClaim> {
    synthetic_claims_for_nodes(graph, cycle.to_vec())
}

pub(crate) fn synthetic_claims_for_cycles(
    graph: &GovernanceGraph,
    cycles: &[Vec<crate::NodeId>],
) -> Vec<GovernanceClaim> {
    let node_ids = cycles
        .iter()
        .flat_map(|cycle| cycle.iter().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    synthetic_claims_for_nodes(graph, node_ids)
}

fn synthetic_claims_for_nodes(
    graph: &GovernanceGraph,
    mut node_ids: Vec<crate::NodeId>,
) -> Vec<GovernanceClaim> {
    node_ids.sort();
    let metric_fields = all_metric_fields_for_nodes(graph, &node_ids);
    let mut claims = vec![baseline_claim(&metric_fields)];

    for node_id in node_ids {
        if let Some(GovernanceNode::Binary { id, gates, .. }) = graph.nodes.get(&node_id) {
            for (index, gate) in gates.iter().enumerate() {
                claims.push(claim_for_gate(
                    &format!("{id}-gate-{index}"),
                    gate,
                    &metric_fields,
                    index,
                ));
            }
        }
    }

    claims.sort_by(|left, right| left.claimant_id.cmp(&right.claimant_id));
    claims
}

fn all_metric_fields_for_nodes(graph: &GovernanceGraph, node_ids: &[crate::NodeId]) -> Vec<String> {
    let mut fields = node_ids
        .iter()
        .filter_map(|node_id| graph.nodes.get(node_id))
        .flat_map(|node| match node {
            GovernanceNode::Binary { gates, .. } => gates
                .iter()
                .filter_map(|gate| match gate {
                    Gate::ThresholdGate { field, .. } | Gate::PeerRelative { field, .. } => {
                        Some(field.clone())
                    }
                    Gate::PrefixMatch { .. }
                    | Gate::ExactMatch { .. }
                    | Gate::ContentMatch { .. } => None,
                })
                .collect::<Vec<_>>(),
            GovernanceNode::Proportional { .. } | GovernanceNode::Threshold { .. } => Vec::new(),
        })
        .collect::<Vec<_>>();
    fields.sort();
    fields.dedup();
    fields
}

fn graph_fields(claims: &[GovernanceClaim]) -> BTreeSet<String> {
    let mut fields = BTreeSet::from(["strength".to_string()]);
    for claim in claims {
        fields.extend(claim.metrics.keys().cloned());
    }
    fields
}

fn graph_shocks(fields: &BTreeSet<String>) -> Vec<BinaryShock> {
    fields
        .iter()
        .map(|field| BinaryShock {
            field: field.clone(),
            delta: if field == "strength" { 0.1 } else { 1.0 },
        })
        .collect()
}

fn graph_deltas(fields: &BTreeSet<String>) -> Vec<BinaryDelta> {
    fields
        .iter()
        .map(|field| BinaryDelta {
            field: field.clone(),
            delta: if field == "strength" { 0.1 } else { 1.0 },
        })
        .collect()
}

fn baseline_claim(metric_fields: &[String]) -> GovernanceClaim {
    GovernanceClaim {
        claimant_id: "baseline".to_string(),
        strength: 1.0,
        priority_class: Some("extracted".to_string()),
        path: Some("/workspace/safe.rs".to_string()),
        action: Some("safe_action".to_string()),
        content: Some("safe content".to_string()),
        metrics: metric_fields
            .iter()
            .map(|field| (field.clone(), 0.0))
            .collect::<BTreeMap<_, _>>(),
    }
}

fn claim_for_gate(
    claimant_id: &str,
    gate: &Gate,
    metric_fields: &[String],
    index: usize,
) -> GovernanceClaim {
    let mut claim = baseline_claim(metric_fields);
    claim.claimant_id = claimant_id.to_string();
    claim.strength = 1.0 + index as f64 * 0.05;

    match gate {
        Gate::PrefixMatch { pattern, decision } => {
            claim.path = Some(format!("{pattern}/candidate"));
            apply_decision_metrics(&mut claim, decision);
        }
        Gate::ExactMatch { value, decision } => {
            claim.action = Some(value.clone());
            apply_decision_metrics(&mut claim, decision);
        }
        Gate::ContentMatch { regex, decision } => {
            claim.content = Some(sample_content(regex));
            apply_decision_metrics(&mut claim, decision);
        }
        Gate::ThresholdGate {
            field,
            min,
            decision,
        } => {
            claim
                .metrics
                .insert(field.clone(), if *min <= 0.0 { 1.0 } else { *min });
            apply_decision_metrics(&mut claim, decision);
        }
        Gate::PeerRelative {
            field,
            percentile: _,
            decision,
        } => {
            claim.metrics.insert(field.clone(), 10.0 + index as f64);
            apply_decision_metrics(&mut claim, decision);
        }
    }

    claim
}

fn apply_decision_metrics(claim: &mut GovernanceClaim, decision: &Decision) {
    let field = match decision {
        Decision::Permit => "permit_signal",
        Decision::Deny => "deny_signal",
        Decision::Escalate => "escalate_signal",
    };
    claim.metrics.insert(field.to_string(), 1.0);
}

fn sample_content(regex: &str) -> String {
    let mut value = String::with_capacity(regex.len());
    let mut escaped = false;
    for character in regex.chars() {
        if escaped {
            value.push(character);
            escaped = false;
        } else if character == '\\' {
            escaped = true;
        } else {
            value.push(character);
        }
    }

    if value.trim().is_empty() {
        "safe content".to_string()
    } else {
        value
    }
}

#[cfg(test)]
mod tests {
    use super::{ExtractionAxiomResult, protocol_can_extract_compile, skipped_axiom};
    use crate::{Claim, Counterexample, Estate, ValidAllocation, Verdict};
    use std::collections::BTreeMap;

    #[test]
    fn compile_rejects_any_failed_axiom() {
        let results = vec![
            passed_axiom("graph consistency"),
            ExtractionAxiomResult {
                axiom: "graph nonvacuity".to_string(),
                verdict: Some(Verdict::Rejected {
                    axiom: "graph nonvacuity".to_string(),
                    counterexample: counterexample(),
                }),
                skipped_reason: None,
            },
        ];

        assert!(!protocol_can_extract_compile(&results, false));
    }

    #[test]
    fn compile_rejects_all_skipped_axioms() {
        let results = vec![
            skipped_axiom("graph consistency", "skipped by fixture"),
            skipped_axiom("graph observable determinacy", "skipped by fixture"),
        ];

        assert!(!protocol_can_extract_compile(&results, false));
    }

    #[test]
    fn compile_accepts_pass_without_rejections() {
        let results = vec![
            passed_axiom("graph consistency"),
            skipped_axiom("graph observable determinacy", "skipped by fixture"),
        ];

        assert!(protocol_can_extract_compile(&results, false));
    }

    fn passed_axiom(name: &str) -> ExtractionAxiomResult {
        ExtractionAxiomResult {
            axiom: name.to_string(),
            verdict: Some(Verdict::Admissible {
                axiom: name.to_string(),
                perturbations_tested: 1,
            }),
            skipped_reason: None,
        }
    }

    fn counterexample() -> Counterexample {
        let claims = vec![Claim::new("alice", 1.0).unwrap()];
        let estate = Estate::new(1.0, "units").unwrap();
        let allocation =
            ValidAllocation::new(BTreeMap::from([("alice".to_string(), 1.0)]).into(), &claims)
                .unwrap();

        Counterexample {
            description: "fixture".to_string(),
            original_claims: claims.clone(),
            original_estate: estate.clone(),
            original_allocation: allocation.clone(),
            perturbed_claims: claims,
            perturbed_estate: estate,
            perturbed_allocation: allocation,
            violation: "fixture".to_string(),
        }
    }
}
