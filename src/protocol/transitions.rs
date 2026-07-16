use crate::{
    EPSILON, GovernanceClaim, GovernanceFactorExposure, GovernanceGraph, GovernanceProperty,
    LegitimacyError, MonitoringSpec, Verdict,
    axioms::{
        diagnostics::{
            binary::{BinaryDelta, BinaryShock},
            graph::{
                consistency::check_graph_consistency,
                monotonicity::monotonicity_check_via_polarity_schema,
                solidarity::check_graph_solidarity,
            },
            strategyproofness::{
                StrategyproofnessOutcome, StrategyproofnessVerdict,
                check_graph_strategyproofness_verdict,
            },
        },
        kernel::{
            AxiomVerdict, check_graph_certifiability, check_graph_compositional_safety,
            check_graph_corrigibility, check_graph_nonvacuity, check_graph_observable_determinacy,
        },
    },
    extract::synthetic_claims,
    graph::traverse,
};
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    time::{SystemTime, UNIX_EPOCH},
};

use super::{
    formats::{
        GovernanceDeclaration, GovernanceDriftAlert, GovernanceRiskReport, PromotionCertificate,
    },
    state::{
        CompiledGraph, DeclaredSacrifice, MonitorConfig, MonitorSession, ProtocolError,
        ProtocolLedger, ProtocolState, SacrificeCertificate, canonical_compiled_rule_hash,
        non_sacrificed_monitoring_properties,
    },
};

pub fn declare(
    graph: GovernanceGraph,
    sacrifices: Vec<DeclaredSacrifice>,
) -> Result<ProtocolState, ProtocolError> {
    declare_with_metadata(
        graph,
        sacrifices,
        "spectral-governance",
        env!("CARGO_PKG_VERSION"),
    )
}

pub fn declare_with_metadata(
    graph: GovernanceGraph,
    sacrifices: Vec<DeclaredSacrifice>,
    graph_name: impl Into<String>,
    graph_version: impl Into<String>,
) -> Result<ProtocolState, ProtocolError> {
    let claims = synthetic_claims(&graph);
    let evaluation = evaluate_graph(&graph, &claims)?;
    for sacrifice in &sacrifices {
        if !evaluation
            .violations
            .contains_key(sacrifice.property.as_str())
        {
            return Err(ProtocolError::PhantomSacrifice {
                property: sacrifice.property.as_str(),
            });
        }
    }
    let declaration = GovernanceDeclaration {
        protocol_version: env!("CARGO_PKG_VERSION").to_string(),
        timestamp: iso8601_timestamp()?,
        graph_name: graph_name.into(),
        graph_version: graph_version.into(),
        graph: graph.clone(),
        sacrifices: sacrifices.clone(),
        spectral_gap: spectral_gap(&graph),
        cv_bound: consistency_vulnerability_bound(&graph, &claims),
    };

    Ok(ProtocolState::Declared {
        graph,
        sacrifices,
        declaration,
    })
}

pub fn compile(declared: ProtocolState) -> Result<ProtocolState, ProtocolError> {
    declared.validate()?;
    let (graph, sacrifices, declaration) = match declared {
        ProtocolState::Declared {
            graph,
            sacrifices,
            declaration,
        } => (graph, sacrifices, declaration),
        other => {
            return Err(ProtocolError::InvalidStateTransition {
                expected: "declared",
                actual: other.name(),
            });
        }
    };

    let claims = synthetic_claims(&graph);
    let evaluation = evaluate_graph(&graph, &claims)?;
    let declared_properties = sacrifices
        .iter()
        .map(|item| item.property.as_str())
        .collect::<BTreeSet<_>>();
    let actual_violations = evaluation
        .violations
        .keys()
        .copied()
        .collect::<BTreeSet<_>>();
    let unsacrificed = actual_violations
        .difference(&declared_properties)
        .filter_map(|property| property_from_str(property))
        .collect::<Vec<_>>();

    if !unsacrificed.is_empty() {
        return Err(ProtocolError::UnsacrificedViolations {
            properties: unsacrificed,
        });
    }

    let sacrifice_certs = sacrifices
        .into_iter()
        .map(|declared_sacrifice| {
            if let Some(violation) = evaluation
                .violations
                .get(declared_sacrifice.property.as_str())
            {
                SacrificeCertificate {
                    property: declared_sacrifice.property,
                    impact_bound: violation.actual_magnitude,
                    source_axiom: violation.source_axiom.clone(),
                    witness: violation.witness.clone(),
                    monitoring_specs: declared_sacrifice
                        .monitoring_specs
                        .into_iter()
                        .map(|spec| MonitoringSpec {
                            threshold: violation.actual_magnitude,
                            ..spec
                        })
                        .collect(),
                }
            } else {
                SacrificeCertificate {
                    property: declared_sacrifice.property,
                    impact_bound: 0.0,
                    source_axiom: declared_sacrifice.property.as_str().to_string(),
                    witness: declared_sacrifice.justification,
                    monitoring_specs: declared_sacrifice.monitoring_specs,
                }
            }
        })
        .collect::<Vec<_>>();

    let axiom_verdicts = evaluation.axiom_verdicts;
    let strategyproofness = evaluation.strategyproofness;
    let compiled_rule_hash =
        canonical_compiled_rule_hash(&graph, &axiom_verdicts, &strategyproofness)?;

    let state = ProtocolState::Compiled {
        compiled_graph: CompiledGraph {
            name: declaration.graph_name.clone(),
            version: declaration.graph_version.clone(),
            graph: graph.clone(),
            axiom_verdicts,
            strategyproofness,
            compiled_rule_hash,
            compiled_at: iso8601_timestamp()?,
        },
        sacrifice_certs,
        declaration,
    };
    state.validate()?;
    Ok(state)
}

pub fn measure(
    compiled: ProtocolState,
    representative_claims: Vec<GovernanceClaim>,
) -> Result<ProtocolState, ProtocolError> {
    compiled.validate()?;
    let (compiled_graph, sacrifice_certs, declaration) = match compiled {
        ProtocolState::Compiled {
            compiled_graph,
            sacrifice_certs,
            declaration,
        } => (compiled_graph, sacrifice_certs, declaration),
        other => {
            return Err(ProtocolError::InvalidStateTransition {
                expected: "compiled",
                actual: other.name(),
            });
        }
    };

    let evaluation = evaluate_graph(&compiled_graph.graph, &representative_claims)?;
    let factor_exposure = GovernanceFactorExposure {
        consistency: verdict_to_exposure(
            &evaluation.axiom_verdicts,
            GovernanceProperty::Consistency,
        ),
        solidarity: verdict_to_exposure(&evaluation.axiom_verdicts, GovernanceProperty::Solidarity),
        monotonicity: verdict_to_exposure(
            &evaluation.axiom_verdicts,
            GovernanceProperty::Monotonicity,
        ),
        strategyproofness: evaluation.strategyproofness.strategyproofness_exposure(),
        nonvacuity: verdict_to_exposure(&evaluation.axiom_verdicts, GovernanceProperty::NonVacuous),
    };
    let risk_report = GovernanceRiskReport {
        factor_exposure,
        spectral_gap: spectral_gap(&compiled_graph.graph),
        cv_bound: consistency_vulnerability_bound(&compiled_graph.graph, &representative_claims),
        localizability_bound: localizability_bound(&compiled_graph.graph, &representative_claims),
    };

    let state = ProtocolState::Measured {
        risk_report,
        factor_exposure,
        compiled_graph,
        sacrifice_certs,
        declaration,
        representative_claims,
    };
    state.validate()?;
    Ok(state)
}

pub fn activate(
    measured: ProtocolState,
    monitor_config: MonitorConfig,
) -> Result<ProtocolState, ProtocolError> {
    measured.validate()?;
    let (
        risk_report,
        factor_exposure,
        compiled_graph,
        sacrifice_certs,
        declaration,
        representative_claims,
    ) = match measured {
        ProtocolState::Measured {
            risk_report,
            factor_exposure,
            compiled_graph,
            sacrifice_certs,
            declaration,
            representative_claims,
        } => (
            risk_report,
            factor_exposure,
            compiled_graph,
            sacrifice_certs,
            declaration,
            representative_claims,
        ),
        other => {
            return Err(ProtocolError::InvalidStateTransition {
                expected: "measured",
                actual: other.name(),
            });
        }
    };

    let monitored_properties = non_sacrificed_monitoring_properties(&sacrifice_certs);
    let session = MonitorSession {
        compiled_graph,
        sacrifice_certs,
        monitored_properties,
        representative_claims,
        interval_seconds: randomized_interval(
            &monitor_config,
            risk_report.spectral_gap,
            factor_exposure.consistency,
        ),
        monitor_config,
    };

    let state = ProtocolState::Live {
        monitor_session: session,
        ledger: ProtocolLedger::default(),
        declaration,
    };
    state.validate()?;
    Ok(state)
}

pub fn check_decision(
    live: ProtocolState,
    claim: GovernanceClaim,
) -> Result<(ProtocolState, PromotionCertificate), ProtocolError> {
    live.validate()?;
    let (mut monitor_session, mut ledger, declaration) = match live {
        ProtocolState::Live {
            monitor_session,
            ledger,
            declaration,
        } => (monitor_session, ledger, declaration),
        other => {
            return Err(ProtocolError::InvalidStateTransition {
                expected: "live",
                actual: other.name(),
            });
        }
    };

    let claims = merge_representative_claims(&monitor_session.representative_claims, claim.clone());
    let traversal = traverse(&monitor_session.compiled_graph.graph, &claims)?;
    let decision = traversal
        .final_decisions
        .get(&claim.claimant_id)
        .cloned()
        .ok_or_else(|| ProtocolError::MissingDecision {
            claimant_id: claim.claimant_id.clone(),
        })?;
    let prev_cert_hash = ledger.head_hash.clone();
    let mut evidence = BTreeMap::new();
    evidence.insert(
        "graph_nodes".to_string(),
        monitor_session.compiled_graph.graph.nodes.len().to_string(),
    );
    evidence.insert(
        "graph_edges".to_string(),
        monitor_session.compiled_graph.graph.edges.len().to_string(),
    );
    evidence.insert(
        "interval_seconds".to_string(),
        monitor_session.interval_seconds.to_string(),
    );

    let certificate = PromotionCertificate {
        rule_name: monitor_session.compiled_graph.name.clone(),
        claimant_id: claim.claimant_id,
        decision,
        outcome_verified: true,
        evidence,
        compiled_rule_hash: monitor_session.compiled_graph.compiled_rule_hash.clone(),
        prev_cert_hash,
        timestamp: iso8601_timestamp()?,
    };
    ledger.head_hash = Some(certificate_hash(&certificate)?);
    ledger.certificates.push(certificate.clone());

    for alert in detect_drift_alerts(&monitor_session, &claims)? {
        ledger.drift_alerts.push(alert);
    }
    monitor_session.representative_claims = claims;

    let state = ProtocolState::Live {
        monitor_session,
        ledger,
        declaration,
    };
    state.validate()?;
    Ok((state, certificate))
}

pub fn report_drift(
    live: ProtocolState,
    violation: GovernanceDriftAlert,
) -> Result<ProtocolState, ProtocolError> {
    live.validate()?;
    let (monitor_session, mut ledger, declaration) = match live {
        ProtocolState::Live {
            monitor_session,
            ledger,
            declaration,
        } => (monitor_session, ledger, declaration),
        other => {
            return Err(ProtocolError::InvalidStateTransition {
                expected: "live",
                actual: other.name(),
            });
        }
    };

    ledger.drift_alerts.push(violation.clone());
    let state = ProtocolState::Drifted {
        drift_report: violation,
        monitor_session,
        ledger,
        declaration,
    };
    state.validate()?;
    Ok(state)
}

pub fn propose_revision(
    drifted: ProtocolState,
    new_graph: GovernanceGraph,
    revised_sacrifices: Vec<DeclaredSacrifice>,
) -> Result<ProtocolState, ProtocolError> {
    drifted.validate()?;
    let declaration = match drifted {
        ProtocolState::Drifted { declaration, .. } => declaration,
        other => {
            return Err(ProtocolError::InvalidStateTransition {
                expected: "drifted",
                actual: other.name(),
            });
        }
    };

    let state = ProtocolState::Recompiling {
        proposed_graph: new_graph,
        sacrifices: revised_sacrifices,
        declaration,
    };
    state.validate()?;
    Ok(state)
}

pub fn recompile(recompiling: ProtocolState) -> Result<ProtocolState, ProtocolError> {
    recompiling.validate()?;
    let (proposed_graph, sacrifices, declaration) = match recompiling {
        ProtocolState::Recompiling {
            proposed_graph,
            sacrifices,
            declaration,
        } => (proposed_graph, sacrifices, declaration),
        other => {
            return Err(ProtocolError::InvalidStateTransition {
                expected: "recompiling",
                actual: other.name(),
            });
        }
    };

    let declared = declare_with_metadata(
        proposed_graph,
        sacrifices,
        declaration.graph_name,
        declaration.graph_version,
    )?;
    compile(declared)
}

#[derive(Debug)]
struct GraphViolation {
    source_axiom: String,
    actual_magnitude: f64,
    witness: String,
}

#[derive(Debug)]
struct GraphEvaluation {
    axiom_verdicts: Vec<Verdict>,
    strategyproofness: StrategyproofnessVerdict,
    violations: HashMap<&'static str, GraphViolation>,
}

fn evaluate_graph(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
) -> Result<GraphEvaluation, ProtocolError> {
    let shocks = graph_shocks(claims);
    let deltas = graph_deltas(claims);
    let consistency = check_graph_consistency(graph, claims)?;
    let solidarity = check_graph_solidarity(graph, claims, &shocks)?;
    let monotonicity =
        monotonicity_check_via_polarity_schema(graph, claims, &deltas, &Default::default())?;
    let certifiability =
        require_protocol_kernel_verdict(check_graph_certifiability(graph, claims)?)?;
    let observable =
        require_protocol_kernel_verdict(check_graph_observable_determinacy(graph, claims)?)?;
    let corrigibility = require_protocol_kernel_verdict(check_graph_corrigibility(graph, claims)?)?;
    let compositional_safety =
        require_protocol_kernel_verdict(check_graph_compositional_safety(graph, claims)?)?;
    let nonvacuity = require_protocol_kernel_verdict(check_graph_nonvacuity(graph, claims, &[])?)?;
    let strategyproofness = check_graph_strategyproofness_verdict(graph, claims)?;
    let axiom_verdicts = vec![
        consistency.clone(),
        solidarity.clone(),
        monotonicity.clone(),
        certifiability.clone(),
        observable.clone(),
        corrigibility.clone(),
        compositional_safety.clone(),
        nonvacuity.clone(),
    ];
    let mut violations = HashMap::new();

    for verdict in &axiom_verdicts {
        if let Verdict::Rejected {
            axiom,
            counterexample,
        } = verdict
            && let Some(property) = property_for_axiom(axiom)
        {
            violations.insert(
                property.as_str(),
                GraphViolation {
                    source_axiom: axiom.clone(),
                    actual_magnitude: counterexample_magnitude(counterexample)?,
                    witness: counterexample.description.clone(),
                },
            );
        }
    }

    if let Some(witness) = strategyproofness.strategyproofness_witness() {
        violations.insert(
            GovernanceProperty::Strategyproofness.as_str(),
            GraphViolation {
                source_axiom: "graph strategyproofness".to_string(),
                actual_magnitude: (witness.manipulated_alloc - witness.true_alloc).abs(),
                witness: format!(
                    "claimant '{}' can improve from {} to {}",
                    witness.claimant, witness.true_alloc, witness.manipulated_alloc
                ),
            },
        );
    }

    Ok(GraphEvaluation {
        axiom_verdicts,
        strategyproofness,
        violations,
    })
}

fn require_protocol_kernel_verdict(verdict: AxiomVerdict) -> Result<Verdict, ProtocolError> {
    match verdict {
        AxiomVerdict::Skipped { axiom, reason } => Err(ProtocolError::SkippedKernelCheck {
            axiom: axiom.graph_axiom_name().to_string(),
            reason,
        }),
        other => Ok(Verdict::try_from(other).expect("non-skipped kernel verdict must convert")),
    }
}

fn graph_shocks(claims: &[GovernanceClaim]) -> Vec<BinaryShock> {
    graph_fields(claims)
        .into_iter()
        .map(|field| BinaryShock {
            delta: if field == "strength" { 0.1 } else { 1.0 },
            field,
        })
        .collect()
}

fn graph_deltas(claims: &[GovernanceClaim]) -> Vec<BinaryDelta> {
    graph_fields(claims)
        .into_iter()
        .map(|field| BinaryDelta {
            delta: if field == "strength" { 0.1 } else { 1.0 },
            field,
        })
        .collect()
}

fn graph_fields(claims: &[GovernanceClaim]) -> BTreeSet<String> {
    let mut fields = BTreeSet::from(["strength".to_string()]);
    for claim in claims {
        fields.extend(claim.metrics.keys().cloned());
    }
    fields
}

fn property_for_axiom(axiom: &str) -> Option<GovernanceProperty> {
    match axiom {
        "graph consistency" => Some(GovernanceProperty::Consistency),
        "graph solidarity" => Some(GovernanceProperty::Solidarity),
        "graph monotonicity" => Some(GovernanceProperty::Monotonicity),
        "graph strategyproofness" => Some(GovernanceProperty::Strategyproofness),
        "graph certifiability" => Some(GovernanceProperty::Certifiability),
        "graph observable determinacy" => Some(GovernanceProperty::ObservableDeterminacy),
        "graph corrigibility" => Some(GovernanceProperty::Corrigibility),
        "graph compositional safety" => Some(GovernanceProperty::CompositionalSafety),
        "graph nonvacuity" => Some(GovernanceProperty::NonVacuous),
        _ => None,
    }
}

fn property_from_str(value: &str) -> Option<GovernanceProperty> {
    match value {
        "consistency" => Some(GovernanceProperty::Consistency),
        "solidarity" => Some(GovernanceProperty::Solidarity),
        "monotonicity" => Some(GovernanceProperty::Monotonicity),
        "strategyproofness" => Some(GovernanceProperty::Strategyproofness),
        "certifiability" => Some(GovernanceProperty::Certifiability),
        "observable_determinacy" => Some(GovernanceProperty::ObservableDeterminacy),
        "corrigibility" => Some(GovernanceProperty::Corrigibility),
        "compositional_safety" => Some(GovernanceProperty::CompositionalSafety),
        "non_vacuous" | "nonvacuous" => Some(GovernanceProperty::NonVacuous),
        _ => None,
    }
}

fn counterexample_magnitude(counterexample: &crate::Counterexample) -> Result<f64, ProtocolError> {
    let mut magnitude = 0.0_f64;
    for (claimant_id, before) in counterexample.original_allocation.iter() {
        if let Some(after) = counterexample
            .perturbed_allocation
            .iter()
            .find_map(|(candidate, value)| (candidate == claimant_id).then_some(*value))
        {
            magnitude = magnitude.max((before - after).abs());
        }
    }
    Ok(magnitude)
}

fn verdict_to_exposure(verdicts: &[Verdict], property: GovernanceProperty) -> f64 {
    let axiom = match property {
        GovernanceProperty::Consistency => "graph consistency",
        GovernanceProperty::Solidarity => "graph solidarity",
        GovernanceProperty::Monotonicity => "graph monotonicity",
        GovernanceProperty::Strategyproofness => "graph strategyproofness",
        GovernanceProperty::Certifiability => "graph certifiability",
        GovernanceProperty::ObservableDeterminacy => "graph observable determinacy",
        GovernanceProperty::Corrigibility => "graph corrigibility",
        GovernanceProperty::CompositionalSafety => "graph compositional safety",
        GovernanceProperty::NonVacuous => "graph nonvacuity",
    };

    if verdicts
        .iter()
        .any(|verdict| matches!(verdict, Verdict::Rejected { axiom: found, .. } if found == axiom))
    {
        1.0
    } else {
        0.0
    }
}

fn detect_drift_alerts(
    monitor_session: &MonitorSession,
    claims: &[GovernanceClaim],
) -> Result<Vec<GovernanceDriftAlert>, ProtocolError> {
    let evaluation = evaluate_graph(&monitor_session.compiled_graph.graph, claims)?;
    let by_property = monitor_session
        .sacrifice_certs
        .iter()
        .map(|cert| (cert.property.as_str(), cert))
        .collect::<HashMap<_, _>>();
    let mut alerts = Vec::new();

    for (property, violation) in evaluation.violations {
        let declared_bound = by_property
            .get(property)
            .map(|cert| cert.impact_bound)
            .unwrap_or(0.0);
        if violation.actual_magnitude > declared_bound + EPSILON {
            alerts.push(GovernanceDriftAlert {
                alert_type: if by_property.contains_key(property) {
                    "bound_breach".to_string()
                } else {
                    "undeclared_violation".to_string()
                },
                property: property_from_str(property).ok_or_else(|| {
                    LegitimacyError::invalid_input(format!(
                        "detect_drift_alerts: unknown governance property '{property}'"
                    ))
                })?,
                declared_bound,
                actual_magnitude: violation.actual_magnitude,
                evidence: BTreeMap::from([("witness".to_string(), violation.witness)]),
                recommended_action: "propose revision and recompile".to_string(),
            });
        }
    }

    Ok(alerts)
}

fn merge_representative_claims(
    representative_claims: &[GovernanceClaim],
    claim: GovernanceClaim,
) -> Vec<GovernanceClaim> {
    let mut claims = representative_claims
        .iter()
        .filter(|existing| existing.claimant_id != claim.claimant_id)
        .cloned()
        .collect::<Vec<_>>();
    claims.push(claim);
    claims
}

fn certificate_hash(certificate: &PromotionCertificate) -> Result<String, ProtocolError> {
    stable_hash(certificate)
}

fn stable_hash<T: Serialize>(value: &T) -> Result<String, ProtocolError> {
    let encoded = serde_json::to_vec(value).map_err(|source| LegitimacyError::Serialize {
        context: "protocol hash payload".to_string(),
        source,
    })?;
    let digest = Sha256::digest(encoded);
    Ok(format!("{digest:x}"))
}

fn spectral_gap(graph: &GovernanceGraph) -> f64 {
    let (laplacian, node_count) = laplacian_matrix(graph);
    if node_count < 2 {
        return 0.0;
    }

    let mut eigenvalues = jacobi_eigenvalues(laplacian);
    eigenvalues.sort_by(f64::total_cmp);
    eigenvalues
        .into_iter()
        .find(|value| *value > EPSILON)
        .unwrap_or(0.0)
}

fn consistency_vulnerability_bound(graph: &GovernanceGraph, claims: &[GovernanceClaim]) -> f64 {
    let signal_range = signal_range(claims);
    let max_degree = max_degree(graph);
    let spectral_gap = spectral_gap(graph);

    if spectral_gap > EPSILON {
        signal_range * max_degree / spectral_gap
    } else {
        signal_range
    }
}

fn localizability_bound(graph: &GovernanceGraph, claims: &[GovernanceClaim]) -> f64 {
    let cv_bound = consistency_vulnerability_bound(graph, claims);
    if cv_bound <= EPSILON {
        return 1.0;
    }

    (0.5 / cv_bound).clamp(0.0, 1.0)
}

fn signal_range(claims: &[GovernanceClaim]) -> f64 {
    let mut min_strength = f64::INFINITY;
    let mut max_strength = f64::NEG_INFINITY;
    for claim in claims {
        min_strength = min_strength.min(claim.strength);
        max_strength = max_strength.max(claim.strength);
    }
    if !min_strength.is_finite() || !max_strength.is_finite() {
        0.0
    } else {
        max_strength - min_strength
    }
}

fn max_degree(graph: &GovernanceGraph) -> f64 {
    let (laplacian, _) = laplacian_matrix(graph);
    laplacian
        .iter()
        .enumerate()
        .map(|(index, row)| row[index])
        .fold(0.0_f64, f64::max)
}

fn laplacian_matrix(graph: &GovernanceGraph) -> (Vec<Vec<f64>>, usize) {
    let node_ids = graph.nodes.keys().cloned().collect::<Vec<_>>();
    let index_by_node = node_ids
        .iter()
        .enumerate()
        .map(|(index, node_id)| (node_id.clone(), index))
        .collect::<HashMap<_, _>>();
    let node_count = node_ids.len();
    let mut adjacency = vec![vec![0.0_f64; node_count]; node_count];

    for edge in &graph.edges {
        if let (Some(&from), Some(&to)) =
            (index_by_node.get(&edge.from), index_by_node.get(&edge.to))
        {
            adjacency[from][to] += 1.0;
            adjacency[to][from] += 1.0;
        }
    }

    let mut laplacian = vec![vec![0.0_f64; node_count]; node_count];
    for row in 0..node_count {
        let degree = adjacency[row].iter().sum::<f64>();
        laplacian[row][row] = degree;
        for col in 0..node_count {
            if row != col {
                laplacian[row][col] = -adjacency[row][col];
            }
        }
    }

    (laplacian, node_count)
}

fn jacobi_eigenvalues(mut matrix: Vec<Vec<f64>>) -> Vec<f64> {
    let n = matrix.len();
    if n == 0 {
        return Vec::new();
    }

    for _ in 0..(n * n * 16).max(16) {
        let mut max_value = 0.0_f64;
        let mut pivot = None;
        for (row, row_values) in matrix.iter().enumerate() {
            for (col, value) in row_values.iter().enumerate().skip(row + 1) {
                let candidate = value.abs();
                if candidate > max_value {
                    max_value = candidate;
                    pivot = Some((row, col));
                }
            }
        }

        let Some((p, q)) = pivot else {
            break;
        };
        if max_value <= 1e-12 {
            break;
        }

        let theta = (matrix[q][q] - matrix[p][p]) / (2.0 * matrix[p][q]);
        let t = if theta >= 0.0 {
            1.0 / (theta + (1.0 + theta * theta).sqrt())
        } else {
            -1.0 / (-theta + (1.0 + theta * theta).sqrt())
        };
        let c = 1.0 / (1.0 + t * t).sqrt();
        let s = t * c;

        let indices = (0..n).collect::<Vec<_>>();
        for index in indices {
            if index == p || index == q {
                continue;
            }
            let aip = matrix[index][p];
            let aiq = matrix[index][q];
            matrix[index][p] = c * aip - s * aiq;
            matrix[p][index] = matrix[index][p];
            matrix[index][q] = c * aiq + s * aip;
            matrix[q][index] = matrix[index][q];
        }

        let app = matrix[p][p];
        let aqq = matrix[q][q];
        let apq = matrix[p][q];
        matrix[p][p] = c * c * app - 2.0 * s * c * apq + s * s * aqq;
        matrix[q][q] = s * s * app + 2.0 * s * c * apq + c * c * aqq;
        matrix[p][q] = 0.0;
        matrix[q][p] = 0.0;
    }

    (0..n).map(|index| matrix[index][index]).collect()
}

fn randomized_interval(config: &MonitorConfig, spectral_gap: f64, exposure: f64) -> u64 {
    let min_interval = config.min_interval_seconds.max(1);
    let max_interval = config.max_interval_seconds.max(min_interval);
    if min_interval == max_interval {
        return min_interval;
    }

    let normalized = (spectral_gap + exposure + config.seed as f64).to_bits();
    min_interval + (normalized % (max_interval - min_interval + 1))
}

pub(crate) fn iso8601_timestamp() -> Result<String, ProtocolError> {
    let seconds = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(LegitimacyError::from)?
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

#[cfg(test)]
mod tests {
    use super::{property_from_str, verdict_to_exposure};
    use crate::{Counterexample, Estate, GovernanceProperty, ValidAllocation, Verdict};
    use std::collections::BTreeMap;

    #[test]
    fn property_from_str_parses_kernel_projection_names() {
        assert_eq!(
            property_from_str("compositional_safety"),
            Some(GovernanceProperty::CompositionalSafety)
        );
    }

    #[test]
    fn verdict_to_exposure_maps_kernel_projection_names() {
        assert_eq!(
            verdict_to_exposure(
                &[Verdict::Rejected {
                    axiom: "graph compositional safety".to_string(),
                    counterexample: counterexample(),
                }],
                GovernanceProperty::CompositionalSafety,
            ),
            1.0
        );
        assert_eq!(
            verdict_to_exposure(
                &[Verdict::Rejected {
                    axiom: "graph consistency".to_string(),
                    counterexample: counterexample(),
                }],
                GovernanceProperty::CompositionalSafety,
            ),
            0.0
        );
    }

    fn counterexample() -> Counterexample {
        let claims = vec![crate::Claim::new("alice", 1.0).unwrap()];
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
