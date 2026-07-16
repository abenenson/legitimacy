use crate::{
    Claim, Claimant, CompiledRule, Counterexample, EPSILON, Estate, Family, GovernanceClaim,
    GovernanceGraph, LegitimacyError, PositiveStrength, Rule, Verdict,
    axioms::diagnostics::{
        binary::{BinaryDelta, BinaryShock},
        graph::{
            consistency::check_graph_consistency, monotonicity::check_graph_monotonicity,
            solidarity::check_graph_solidarity,
        },
        strategyproofness::{
            StrategyproofnessOutcome, StrategyproofnessVerdict,
            check_graph_strategyproofness_verdict,
        },
    },
    axioms::kernel::{
        AxiomVerdict, check_graph_certifiability, check_graph_compositional_safety,
        check_graph_corrigibility, check_graph_nonvacuity, check_graph_observable_determinacy,
    },
    compiler::{CompileOptions, compile, compile_with_options},
    ledger::Ledger,
};
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, BTreeSet},
    time::{SystemTime, UNIX_EPOCH},
};

const DEFAULT_SHOCKS: [f64; 4] = [0.5, 0.75, 1.25, 1.5];
const DEFAULT_STRENGTHENING: [f64; 3] = [0.1, 0.5, 1.0];
const DEFAULT_ALERT_CHANNEL: &str = "governance-risk";
const GRAPH_NAME: &str = "governance-graph";
const GRAPH_VERSION: &str = "derived";

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum GovernanceProperty {
    Consistency,
    Solidarity,
    Monotonicity,
    Strategyproofness,
    Certifiability,
    ObservableDeterminacy,
    Corrigibility,
    CompositionalSafety,
    NonVacuous,
}

impl GovernanceProperty {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Consistency => "consistency",
            Self::Solidarity => "solidarity",
            Self::Monotonicity => "monotonicity",
            Self::Strategyproofness => "strategyproofness",
            Self::Certifiability => "certifiability",
            Self::ObservableDeterminacy => "observable_determinacy",
            Self::Corrigibility => "corrigibility",
            Self::CompositionalSafety => "compositional_safety",
            Self::NonVacuous => "non_vacuous",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "consistency" => Some(Self::Consistency),
            "solidarity" => Some(Self::Solidarity),
            "monotonicity" => Some(Self::Monotonicity),
            "strategyproofness" => Some(Self::Strategyproofness),
            "certifiability" => Some(Self::Certifiability),
            "observable_determinacy" => Some(Self::ObservableDeterminacy),
            "corrigibility" => Some(Self::Corrigibility),
            "compositional_safety" => Some(Self::CompositionalSafety),
            "non_vacuous" | "nonvacuous" => Some(Self::NonVacuous),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum CompiledGovernanceKind {
    Rule,
    Graph,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct MonitoringSpec {
    pub metric: String,
    pub threshold: f64,
    pub frequency_seconds: u64,
    pub alert_channel: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SacrificeProvenance {
    pub compiled_kind: CompiledGovernanceKind,
    pub compiled_name: String,
    pub compiled_version: String,
    pub compiled_at: String,
    pub family_description: String,
    pub source_axiom: String,
    pub witness: String,
}

/// Compiled sacrifice record persisted to the ledger. Unlike protocol graph
/// declarations, this carries observed impact bounds and provenance.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct DeclaredSacrifice {
    pub sacrificed_property: GovernanceProperty,
    pub justification: String,
    pub impact_bound: f64,
    pub monitoring_plan: Vec<MonitoringSpec>,
    pub provenance: SacrificeProvenance,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompiledGraph {
    pub name: String,
    pub version: String,
    pub axiom_verdicts: Vec<Verdict>,
    pub strategyproofness: StrategyproofnessVerdict,
    pub family_description: String,
    pub compiled_at: String,
}

impl CompiledGraph {
    pub fn is_admissible(&self) -> bool {
        self.axiom_verdicts
            .iter()
            .all(|verdict| matches!(verdict, Verdict::Admissible { .. }))
            && matches!(
                self.strategyproofness,
                StrategyproofnessVerdict::Strategyproof
            )
    }

    pub fn violations(&self) -> Vec<&Counterexample> {
        self.axiom_verdicts
            .iter()
            .filter_map(|verdict| match verdict {
                Verdict::Rejected { counterexample, .. } => Some(counterexample),
                Verdict::Admissible { .. } => None,
            })
            .collect()
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "compiled_kind", content = "compiled", rename_all = "snake_case")]
pub enum CompiledGovernance {
    Rule(CompiledRule),
    Graph(CompiledGraph),
}

impl CompiledGovernance {
    pub fn kind(&self) -> CompiledGovernanceKind {
        match self {
            Self::Rule(_) => CompiledGovernanceKind::Rule,
            Self::Graph(_) => CompiledGovernanceKind::Graph,
        }
    }

    pub fn name(&self) -> &str {
        match self {
            Self::Rule(compiled) => &compiled.name,
            Self::Graph(compiled) => &compiled.name,
        }
    }

    pub fn version(&self) -> &str {
        match self {
            Self::Rule(compiled) => &compiled.version,
            Self::Graph(compiled) => &compiled.version,
        }
    }

    pub fn family_description(&self) -> &str {
        match self {
            Self::Rule(compiled) => &compiled.family_description,
            Self::Graph(compiled) => &compiled.family_description,
        }
    }

    pub fn compiled_at(&self) -> &str {
        match self {
            Self::Rule(compiled) => &compiled.compiled_at,
            Self::Graph(compiled) => &compiled.compiled_at,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeclaredSacrificesCertificate {
    pub compiled: CompiledGovernance,
    pub sacrifices: Vec<DeclaredSacrifice>,
}

pub trait SacrificeCompileTarget {
    type Claim;

    fn compile_declared_sacrifices(
        &self,
        claims: &[Self::Claim],
        estate: &Estate,
    ) -> Result<DeclaredSacrificesCertificate, LegitimacyError>;

    fn recompile_declared_sacrifices_with_revised_ledger(
        &self,
        claims: &[Self::Claim],
        estate: &Estate,
        revised_sacrifices: Vec<DeclaredSacrifice>,
    ) -> Result<DeclaredSacrificesCertificate, LegitimacyError>;
}

pub struct RevisedSacrificeRecompile<'a, T: SacrificeCompileTarget> {
    pub target: &'a T,
    pub claims: &'a [T::Claim],
    pub estate: &'a Estate,
    pub revised_sacrifices: Vec<DeclaredSacrifice>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RevisedSacrificeRecompileOutput {
    pub certificate: DeclaredSacrificesCertificate,
}

impl RevisedSacrificeRecompileOutput {
    pub fn into_certificate(self) -> DeclaredSacrificesCertificate {
        self.certificate
    }
}

pub fn compile_with_sacrifices<T: SacrificeCompileTarget>(
    target: &T,
    claims: &[T::Claim],
    estate: &Estate,
) -> Result<DeclaredSacrificesCertificate, LegitimacyError> {
    compile_with_sacrifices_and_monitor(target, claims, estate)
}

/// Compile governance with Basel-style disclosure semantics: declare the
/// sacrificed properties, compute their observed perturbation exposure bounds,
/// and attach machine-readable monitoring thresholds for breach detection.
pub fn compile_with_sacrifices_and_monitor<T: SacrificeCompileTarget>(
    target: &T,
    claims: &[T::Claim],
    estate: &Estate,
) -> Result<DeclaredSacrificesCertificate, LegitimacyError> {
    target.compile_declared_sacrifices(claims, estate)
}

/// Recompile governance after a human or supervisory revision to the sacrifice
/// ledger. The supplied ledger supersedes the sacrifices detected by the
/// compiler while the compiled governance payload is recomputed from `target`.
pub fn recompile_with_revised_sacrifice<T: SacrificeCompileTarget>(
    input: RevisedSacrificeRecompile<'_, T>,
) -> Result<RevisedSacrificeRecompileOutput, LegitimacyError> {
    Ok(RevisedSacrificeRecompileOutput {
        certificate: input
            .target
            .recompile_declared_sacrifices_with_revised_ledger(
                input.claims,
                input.estate,
                input.revised_sacrifices,
            )?,
    })
}

pub fn compile_with_sacrifices_with_family(
    rule: &Rule,
    claims: &[Claim],
    claimants: &[Claimant],
    estate: &Estate,
    family: &Family,
) -> Result<DeclaredSacrificesCertificate, LegitimacyError> {
    compile_with_sacrifices_with_family_and_options(
        rule,
        claims,
        claimants,
        estate,
        family,
        CompileOptions::default(),
    )
}

pub fn compile_with_sacrifices_with_family_and_options(
    rule: &Rule,
    claims: &[Claim],
    claimants: &[Claimant],
    estate: &Estate,
    family: &Family,
    options: CompileOptions,
) -> Result<DeclaredSacrificesCertificate, LegitimacyError> {
    let compiled = compile_with_options(rule, claims, estate, claimants, family, options)?;
    let sacrifices = sacrifices_from_rule(&compiled);
    issue_certificate(CompiledGovernance::Rule(compiled), sacrifices)
}

fn compile_with_revised_sacrifices_with_family(
    rule: &Rule,
    claims: &[Claim],
    claimants: &[Claimant],
    estate: &Estate,
    family: &Family,
    revised_sacrifices: Vec<DeclaredSacrifice>,
) -> Result<DeclaredSacrificesCertificate, LegitimacyError> {
    let compiled = compile(rule, claims, estate, claimants, family)?;
    issue_certificate(CompiledGovernance::Rule(compiled), revised_sacrifices)
}

pub fn compile_graph_with_sacrifices(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
    _estate: &Estate,
) -> Result<DeclaredSacrificesCertificate, LegitimacyError> {
    let compiled = compile_graph_payload(graph, claims)?;
    let sacrifices = sacrifices_from_graph(&compiled);
    issue_certificate(CompiledGovernance::Graph(compiled), sacrifices)
}

fn compile_graph_with_revised_sacrifices(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
    _estate: &Estate,
    revised_sacrifices: Vec<DeclaredSacrifice>,
) -> Result<DeclaredSacrificesCertificate, LegitimacyError> {
    let compiled = compile_graph_payload(graph, claims)?;
    issue_certificate(CompiledGovernance::Graph(compiled), revised_sacrifices)
}

fn compile_graph_payload(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
) -> Result<CompiledGraph, LegitimacyError> {
    let fields = graph_fields(claims);
    let shocks = graph_shocks(&fields);
    let deltas = graph_deltas(&fields);
    Ok(CompiledGraph {
        name: GRAPH_NAME.to_string(),
        version: GRAPH_VERSION.to_string(),
        axiom_verdicts: vec![
            check_graph_consistency(graph, claims)?,
            check_graph_solidarity(graph, claims, &shocks)?,
            check_graph_monotonicity(graph, claims, &deltas)?,
            require_graph_kernel_verdict(check_graph_certifiability(graph, claims)?)?,
            require_graph_kernel_verdict(check_graph_observable_determinacy(graph, claims)?)?,
            require_graph_kernel_verdict(check_graph_corrigibility(graph, claims)?)?,
            require_graph_kernel_verdict(check_graph_compositional_safety(graph, claims)?)?,
            require_graph_kernel_verdict(check_graph_nonvacuity(graph, claims, &[])?)?,
        ],
        strategyproofness: check_graph_strategyproofness_verdict(graph, claims)?,
        family_description: format!(
            "derived_fields={:?}, shocks={:?}, deltas={:?}",
            fields,
            shocks
                .iter()
                .map(|shock| format!("{}:{:.2}", shock.field, shock.delta))
                .collect::<Vec<_>>(),
            deltas
                .iter()
                .map(|delta| format!("{}:{:.2}", delta.field, delta.delta))
                .collect::<Vec<_>>(),
        ),
        compiled_at: unix_timestamp()?,
    })
}

fn require_graph_kernel_verdict(verdict: AxiomVerdict) -> Result<Verdict, LegitimacyError> {
    Verdict::try_from(verdict).map_err(|skipped| {
        LegitimacyError::invalid_input(format!(
            "skipped {} during graph sacrifice compilation: {}",
            skipped.axiom.graph_axiom_name(),
            skipped.reason
        ))
    })
}

impl SacrificeCompileTarget for Rule {
    type Claim = Claim;

    fn compile_declared_sacrifices(
        &self,
        claims: &[Self::Claim],
        estate: &Estate,
    ) -> Result<DeclaredSacrificesCertificate, LegitimacyError> {
        let claimants = default_claimants(self, claims);
        let family = default_family()?;
        compile_with_sacrifices_with_family(self, claims, &claimants, estate, &family)
    }

    fn recompile_declared_sacrifices_with_revised_ledger(
        &self,
        claims: &[Self::Claim],
        estate: &Estate,
        revised_sacrifices: Vec<DeclaredSacrifice>,
    ) -> Result<DeclaredSacrificesCertificate, LegitimacyError> {
        let claimants = default_claimants(self, claims);
        let family = default_family()?;
        compile_with_revised_sacrifices_with_family(
            self,
            claims,
            &claimants,
            estate,
            &family,
            revised_sacrifices,
        )
    }
}

impl SacrificeCompileTarget for GovernanceGraph {
    type Claim = GovernanceClaim;

    fn compile_declared_sacrifices(
        &self,
        claims: &[Self::Claim],
        estate: &Estate,
    ) -> Result<DeclaredSacrificesCertificate, LegitimacyError> {
        compile_graph_with_sacrifices(self, claims, estate)
    }

    fn recompile_declared_sacrifices_with_revised_ledger(
        &self,
        claims: &[Self::Claim],
        estate: &Estate,
        revised_sacrifices: Vec<DeclaredSacrifice>,
    ) -> Result<DeclaredSacrificesCertificate, LegitimacyError> {
        compile_graph_with_revised_sacrifices(self, claims, estate, revised_sacrifices)
    }
}

fn issue_certificate(
    compiled: CompiledGovernance,
    sacrifices: Vec<DeclaredSacrifice>,
) -> Result<DeclaredSacrificesCertificate, LegitimacyError> {
    let certificate = DeclaredSacrificesCertificate {
        compiled,
        sacrifices,
    };

    if !certificate.sacrifices.is_empty() {
        Ledger::open_default()?.record_declared_sacrifices(&certificate)?;
    }

    Ok(certificate)
}

fn sacrifices_from_rule(compiled: &CompiledRule) -> Vec<DeclaredSacrifice> {
    sacrifices_from_axioms(
        compiled_metadata(
            CompiledGovernanceKind::Rule,
            &compiled.name,
            &compiled.version,
            &compiled.family_description,
            &compiled.compiled_at,
        ),
        &compiled.axiom_verdicts,
        &compiled.strategyproofness,
    )
}

fn sacrifices_from_graph(compiled: &CompiledGraph) -> Vec<DeclaredSacrifice> {
    sacrifices_from_axioms(
        compiled_metadata(
            CompiledGovernanceKind::Graph,
            &compiled.name,
            &compiled.version,
            &compiled.family_description,
            &compiled.compiled_at,
        ),
        &compiled.axiom_verdicts,
        &compiled.strategyproofness,
    )
}

fn sacrifices_from_axioms(
    metadata: CompiledMetadata<'_>,
    axiom_verdicts: &[Verdict],
    strategyproofness: &StrategyproofnessVerdict,
) -> Vec<DeclaredSacrifice> {
    let mut sacrifices = axiom_verdicts
        .iter()
        .filter_map(|verdict| match verdict {
            Verdict::Rejected {
                axiom,
                counterexample,
            } => property_for_axiom(axiom).map(|property| {
                counterexample_sacrifice(metadata, property, axiom, counterexample)
            }),
            Verdict::Admissible { .. } => None,
        })
        .collect::<Vec<_>>();

    if let Some(witness) = strategyproofness.strategyproofness_witness() {
        let threshold = (witness.reported - witness.true_strength).abs();
        sacrifices.push(DeclaredSacrifice {
            sacrificed_property: GovernanceProperty::Strategyproofness,
            justification: format!(
                "Claimant '{}' can improve its outcome by misreporting strength from {} to {}, moving from {} to {}.",
                witness.claimant,
                witness.true_strength,
                witness.reported,
                witness.true_alloc,
                witness.manipulated_alloc
            ),
            impact_bound: threshold,
            monitoring_plan: vec![MonitoringSpec {
                metric: format!(
                    "{}.claim_strength_delta",
                    GovernanceProperty::Strategyproofness.as_str()
                ),
                threshold,
                frequency_seconds: monitoring_frequency_seconds(
                    GovernanceProperty::Strategyproofness,
                ),
                alert_channel: monitoring_alert_channel(GovernanceProperty::Strategyproofness),
            }],
            provenance: SacrificeProvenance {
                compiled_kind: metadata.kind,
                compiled_name: metadata.name.to_string(),
                compiled_version: metadata.version.to_string(),
                compiled_at: metadata.compiled_at.to_string(),
                family_description: metadata.family_description.to_string(),
                source_axiom: "strategyproofness".to_string(),
                witness: format!(
                    "manipulable claimant={}, true_strength={}, reported={}",
                    witness.claimant, witness.true_strength, witness.reported
                ),
            },
        });
    }

    sacrifices
}

fn property_for_axiom(axiom: &str) -> Option<GovernanceProperty> {
    let lower = axiom.to_ascii_lowercase();
    if lower.contains("compositional safety") {
        Some(GovernanceProperty::CompositionalSafety)
    } else if lower.contains("certifiability") || lower.contains("certifiable") {
        Some(GovernanceProperty::Certifiability)
    } else if lower.contains("corrigibility") || lower.contains("corrigible") {
        Some(GovernanceProperty::Corrigibility)
    } else if lower.contains("observable determinacy") || lower.contains("observable_determinacy") {
        Some(GovernanceProperty::ObservableDeterminacy)
    } else if lower.contains("nonvacu") || lower.contains("non-vacu") || lower.contains("non_vacu")
    {
        Some(GovernanceProperty::NonVacuous)
    } else if lower.contains("consistency") {
        Some(GovernanceProperty::Consistency)
    } else if lower.contains("solidarity") {
        Some(GovernanceProperty::Solidarity)
    } else if lower.contains("monotonicity") {
        Some(GovernanceProperty::Monotonicity)
    } else {
        None
    }
}

fn counterexample_sacrifice(
    metadata: CompiledMetadata<'_>,
    sacrificed_property: GovernanceProperty,
    axiom: &str,
    counterexample: &Counterexample,
) -> DeclaredSacrifice {
    let monitoring_plan = monitoring_plan_from_counterexample(sacrificed_property, counterexample);
    let impact_bound = monitoring_plan
        .iter()
        .map(|spec| spec.threshold)
        .fold(0.0_f64, f64::max);

    DeclaredSacrifice {
        sacrificed_property,
        justification: format!(
            "{} Witness: {}",
            counterexample.violation, counterexample.description
        ),
        impact_bound,
        monitoring_plan,
        provenance: SacrificeProvenance {
            compiled_kind: metadata.kind,
            compiled_name: metadata.name.to_string(),
            compiled_version: metadata.version.to_string(),
            compiled_at: metadata.compiled_at.to_string(),
            family_description: metadata.family_description.to_string(),
            source_axiom: axiom.to_string(),
            witness: counterexample.description.clone(),
        },
    }
}

fn monitoring_plan_from_counterexample(
    property: GovernanceProperty,
    counterexample: &Counterexample,
) -> Vec<MonitoringSpec> {
    let mut metrics = BTreeMap::new();
    let estate_delta = estate_relative_change(counterexample);
    if estate_delta > EPSILON {
        metrics.insert("estate_relative_change".to_string(), estate_delta);
    }

    let strength_delta = max_strength_delta(counterexample);
    if strength_delta > EPSILON {
        metrics.insert("claim_strength_delta".to_string(), strength_delta);
    }

    for (metric, threshold) in max_claim_metric_deltas(counterexample) {
        if threshold > EPSILON {
            metrics.insert(format!("claim_metric_delta.{metric}"), threshold);
        }
    }

    let frequency_seconds = monitoring_frequency_seconds(property);
    let alert_channel = monitoring_alert_channel(property);

    metrics
        .into_iter()
        .map(|(metric, threshold)| MonitoringSpec {
            metric: format!("{}.{}", property.as_str(), metric),
            threshold,
            frequency_seconds,
            alert_channel: alert_channel.clone(),
        })
        .collect()
}

fn estate_relative_change(counterexample: &Counterexample) -> f64 {
    let original = counterexample.original_estate.total.value();
    let perturbed = counterexample.perturbed_estate.total.value();
    if original <= EPSILON {
        0.0
    } else {
        ((perturbed / original) - 1.0).abs()
    }
}

fn max_strength_delta(counterexample: &Counterexample) -> f64 {
    claim_ids(counterexample)
        .into_iter()
        .map(|claimant_id| {
            let original = find_claim(&counterexample.original_claims, &claimant_id)
                .map(|claim| claim.strength.value())
                .unwrap_or(0.0);
            let perturbed = find_claim(&counterexample.perturbed_claims, &claimant_id)
                .map(|claim| claim.strength.value())
                .unwrap_or(0.0);
            (perturbed - original).abs()
        })
        .fold(0.0_f64, f64::max)
}

fn max_claim_metric_deltas(counterexample: &Counterexample) -> BTreeMap<String, f64> {
    let mut deltas = BTreeMap::new();

    for claimant_id in claim_ids(counterexample) {
        let original = find_claim(&counterexample.original_claims, &claimant_id);
        let perturbed = find_claim(&counterexample.perturbed_claims, &claimant_id);
        let metric_names = original
            .iter()
            .flat_map(|claim| claim.metrics.keys())
            .chain(perturbed.iter().flat_map(|claim| claim.metrics.keys()))
            .cloned()
            .collect::<BTreeSet<_>>();

        for metric_name in metric_names {
            let before = original
                .and_then(|claim| claim.metrics.get(&metric_name))
                .copied()
                .unwrap_or(0.0);
            let after = perturbed
                .and_then(|claim| claim.metrics.get(&metric_name))
                .copied()
                .unwrap_or(0.0);
            let delta = (after - before).abs();
            deltas
                .entry(metric_name)
                .and_modify(|current: &mut f64| *current = (*current).max(delta))
                .or_insert(delta);
        }
    }

    deltas
}

fn claim_ids(counterexample: &Counterexample) -> BTreeSet<String> {
    counterexample
        .original_claims
        .iter()
        .chain(counterexample.perturbed_claims.iter())
        .map(|claim| claim.claimant_id.clone())
        .collect()
}

fn find_claim<'a>(claims: &'a [Claim], claimant_id: &str) -> Option<&'a Claim> {
    claims.iter().find(|claim| claim.claimant_id == claimant_id)
}

fn monitoring_frequency_seconds(property: GovernanceProperty) -> u64 {
    match property {
        GovernanceProperty::Strategyproofness => 60,
        GovernanceProperty::Certifiability => 60,
        GovernanceProperty::ObservableDeterminacy => 60,
        GovernanceProperty::Corrigibility => 60,
        GovernanceProperty::CompositionalSafety => 60,
        GovernanceProperty::NonVacuous => 60,
        GovernanceProperty::Consistency => 900,
        GovernanceProperty::Solidarity | GovernanceProperty::Monotonicity => 300,
    }
}

fn monitoring_alert_channel(property: GovernanceProperty) -> String {
    format!("{DEFAULT_ALERT_CHANNEL}.{}", property.as_str())
}

fn default_claimants(rule: &Rule, claims: &[Claim]) -> Vec<Claimant> {
    let default_priority_class = rule
        .priority_classes
        .first()
        .cloned()
        .unwrap_or_else(|| "standard".to_string());

    claims
        .iter()
        .map(|claim| Claimant {
            id: claim.claimant_id.clone(),
            priority_class: default_priority_class.clone(),
            attributes: Default::default(),
        })
        .collect()
}

fn default_family() -> Result<Family, LegitimacyError> {
    Ok(Family {
        reductions: true,
        shocks: DEFAULT_SHOCKS.to_vec(),
        strengthening_deltas: DEFAULT_STRENGTHENING
            .iter()
            .copied()
            .map(PositiveStrength::new)
            .collect::<Result<Vec<_>, _>>()?,
        monotonicity_inversion: false,
    })
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

fn unix_timestamp() -> Result<String, LegitimacyError> {
    Ok(SystemTime::now()
        .duration_since(UNIX_EPOCH)?
        .as_secs()
        .to_string())
}

#[derive(Clone, Copy)]
struct CompiledMetadata<'a> {
    kind: CompiledGovernanceKind,
    name: &'a str,
    version: &'a str,
    family_description: &'a str,
    compiled_at: &'a str,
}

fn compiled_metadata<'a>(
    kind: CompiledGovernanceKind,
    name: &'a str,
    version: &'a str,
    family_description: &'a str,
    compiled_at: &'a str,
) -> CompiledMetadata<'a> {
    CompiledMetadata {
        kind,
        name,
        version,
        family_description,
        compiled_at,
    }
}

#[cfg(test)]
mod tests {
    use super::{GovernanceProperty, property_for_axiom};

    #[test]
    fn property_for_axiom_maps_kernel_projections_before_substrings() {
        assert_eq!(
            property_for_axiom("graph compositional safety witness"),
            Some(GovernanceProperty::CompositionalSafety)
        );
        assert_eq!(
            property_for_axiom("graph certifiability witness"),
            Some(GovernanceProperty::Certifiability)
        );
    }
}
