//! legitimacy - research artifact for semantic legitimacy kernels.
//!
//! Checks compiled governance artifacts against the five runtime obligations:
//! certifiability, governance observability, corrigibility, compositional
//! safety, and non-vacuity. Reports graph-diagnostic axiom verdicts,
//! bridge-derived strategyproofness diagnostics, spectral bounds, and declared
//! sacrifice certificates.

extern crate self as legitimacy;

pub mod axioms;
pub mod behavioral;
pub mod certificate;
pub mod cli_runtime;
pub mod compiler;
pub mod error;
pub mod extract;
pub mod factor;
pub mod graph;
pub mod harness;
pub mod harness_impls;
pub mod ledger;
pub mod mechanism;
pub mod monitor;
pub mod paradox;
pub mod policy;
pub mod protocol;
pub mod rules;
pub mod sacrifice;
pub mod safety_spec_reduction;
pub mod spectral;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    iter::Sum,
    ops::{Deref, DerefMut, Div, Mul, Sub},
    sync::Arc,
};

pub use axioms::diagnostics::consistency::{
    ConsistencyComplexity, ConsistencyMode, ConsistencyRational, FullConsistencyAudit,
    FullConsistencyOptions, RationalAllocation, RationalClaim, RationalConsistencyCounterexample,
    RationalEstate, RationalFullConsistencyAuditArtifact, RationalFullConsistencyVerdict,
    check_bounded_consistency, check_consistency, check_full_consistency,
    check_full_consistency_audit, check_full_consistency_rational, check_singles_pairs_consistency,
};
pub use axioms::diagnostics::graph::{
    consistency::check_graph_consistency, monotonicity::check_graph_monotonicity,
    solidarity::check_graph_solidarity, strategyproofness::check_graph_strategyproofness,
};
pub use axioms::diagnostics::strategyproofness::{
    StrategyproofnessOutcome, StrategyproofnessVerdict, StrategyproofnessWitness,
    check_binary_strategyproofness, check_graph_strategyproofness_verdict, check_strategyproofness,
};
pub use certificate::{CertificationContext, certify};
pub use compiler::CompileOptions;
pub use error::LegitimacyError;
pub use extract::kernelization::{
    AuthorityEdge, AuthorityGraph, AuthorityNodeId, BypassPathWitness,
    GovernanceKernelizationObservation, HiddenAuthorityCertificate, HiddenOverrideWitness,
    KernelizationCleanWitness, KernelizationExtractorContract, KernelizationExtractorResult,
    KernelizationHonestyError, SemanticBridgeFailureWitness, SemanticFailureLocus,
    SourceEdgeDerivation, SourceEvidenceGapWitness, UnmodeledEdgeWitness,
    authority_edge_difference, authority_extensionally_equivalent, authority_override_difference,
    authority_path_permitted, bypass_path_minimal, bypass_path_observation, clean_authority_graph,
    clean_kernelization_observation, edge, hidden_override_dominates_pair,
    hidden_override_observation, is_edge_permitted_bypass, is_edge_permitted_route,
    kernelization_clean, kernelization_honesty, minimal_hidden_authority, path_authority_edges,
    proper_route_sublist, route_direct_edge, route_sublists, route_target,
    semantic_bridge_failure_observation, semantic_failure_locus_fails,
    semantic_failure_locus_minimal, source_derives_edge, source_evidence_complete,
    source_evidence_derivable, source_gap_observation, unmodeled_edge_observation,
};
pub use extract::spectral::SpectralAnalysis;
pub use extract::{
    AliasHintOverlay, AstHashFile, AstTheoremWitness, AstWitnessVerification,
    BoundaryCausalSafetyAssessment, ClaimCorpusProvenance, EdgeResolutionKind,
    ExtractionCoverageReport, ExtractionEvidenceTier, ExtractionFileReport, ExtractionFileStatus,
    ExtractionOptions, ExtractionReviewOverlay, ExtractionSourceLanguage, GovernanceAuditReport,
    GovernanceExtractionArtifacts, GovernanceExtractionReport, OBSERVED_RUNTIME_CLAIMS_FILENAME,
    OBSERVED_RUNTIME_CORPUS_SCHEMA_VERSION, OBSERVED_RUNTIME_MANIFEST_FILENAME,
    ObservedRuntimeClaimRecord, ObservedRuntimeCorpusManifest, ObservedRuntimeCorpusPack,
    ObservedRuntimeRedactionMetadata, ProtocolStateAssessment, RecognitionConfidence,
    RecognizedEdgeProvenance, RecognizedNodeProvenance, RecommendedSacrifice, ResolutionIssue,
    ResolutionIssueKind, ReviewedEdgeOverlay, ReviewedNodeOverlay, UngovernedDependency,
    analyze_extraction, analyze_extraction_with_review, ast_theorem_witness, audit_extracted_graph,
    audit_extracted_graph_with_review, audit_governance_graph, build_codex_oss_story_corpus_pack,
    canonical_ast_fingerprint, extract_governance, extract_governance_artifacts,
    extract_governance_artifacts_with_review, import_codex_oss_story_corpus_pack,
    load_observed_runtime_corpus_pack, observed_runtime_claims_path,
    observed_runtime_manifest_path, verify_ast_theorem_witness, write_observed_runtime_corpus_pack,
};
pub use factor::{
    GovernanceFactorExposure, compute_factor_exposure, compute_factor_exposure_with_family,
    compute_factor_exposure_with_family_and_options,
};
pub use graph::cycle::{check_cycle_admissibility, detect_cycles};
pub use graph::{
    Decision, EdgeTransform, Gate, GateLogic, GovernanceClaim, GovernanceEdge, GovernanceGraph,
    GovernanceNode, GraphBuilder, NodeId, TraversalResult, traverse, validate_governance_graph,
};
pub use ledger::{
    ChainVerificationResult, Ledger, LedgerAuditReport, LedgerQuery, TableChainStatus,
};
pub use monitor::{
    GovernanceDriftEvent, GovernanceDriftMonitor, GovernanceEventSource, GovernanceMonitoringEvent,
    MonitorSession, compiled_graph_from_rule, default_policy_event_source_path, monitor,
};
pub use paradox::{
    GraphParadoxType, compositional_alabama, feedback_monotonicity, path_dependence,
};
pub use protocol::{
    CompiledGraph as ProtocolCompiledGraph, DeclaredSacrifice as ProtocolDeclaredSacrifice,
    GovernanceDeclaration, GovernanceDriftAlert, GovernanceRiskReport,
    GraphSacrifice as ProtocolGraphSacrifice, MonitorConfig,
    MonitorSession as ProtocolMonitorSession, PromotionCertificate, ProtocolError, ProtocolLedger,
    ProtocolState, SacrificeCertificate, SacrificeDeclaration as ProtocolSacrificeDeclaration,
    SupervisoryAction, SupervisoryIntervention, SupervisoryPostcondition, activate, check_decision,
    compile as compile_protocol, declare, declare_with_metadata, measure as measure_protocol,
    propose_revision, recompile, report_drift, supervise,
};
pub use sacrifice::{
    CompiledGovernance, CompiledGovernanceKind, CompiledGraph, DeclaredSacrifice,
    DeclaredSacrificesCertificate, GovernanceProperty, MonitoringSpec, RevisedSacrificeRecompile,
    RevisedSacrificeRecompileOutput, SacrificeCompileTarget, SacrificeProvenance,
    compile_graph_with_sacrifices, compile_with_sacrifices, compile_with_sacrifices_and_monitor,
    compile_with_sacrifices_with_family, compile_with_sacrifices_with_family_and_options,
    recompile_with_revised_sacrifice,
};
pub use safety_spec_reduction::{
    ExtractorInput, ForcedSacrificesDeclaredWitness, KernelAuditConjunction,
    ReachableStateSafetyWitness, RuleLayerKernelArtifact, RuleLayerKernelArtifactClaims,
    RuleLayerKernelArtifactParts, RuleLayerKernelArtifactValidator,
    RuleLayerKernelArtifactVerificationError, RuleLayerKernelAuditObligations,
    RuntimeKernelWitness, SemanticBridgeWitness, SemanticKernelWitness,
    StructuralKernelArtifactValidator, autogen_extractor_input,
    malformed_safety_spec_reduction_artifact, malformed_safety_spec_reduction_input,
    no_silent_rule_layer_degradation, safety_spec_reduces_to_kernel_audit,
    safety_spec_reduction_example_artifact, safety_spec_reduction_example_obligations,
    semantic_bridge_failure_artifact,
};

/// Default tolerance for axiom checks.
pub const EPSILON: f64 = 1e-9;

/// A unique identifier for a claimant (agent, policy, user, etc.).
pub type ClaimantId = String;

/// A claimant competing for a share of the estate.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct Claimant {
    pub id: ClaimantId,
    pub priority_class: String,
    pub attributes: BTreeMap<String, f64>,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, PartialOrd)]
#[serde(try_from = "f64", into = "f64")]
pub struct PositiveStrength(f64);

impl PositiveStrength {
    #[tracing::instrument(fields(value))]
    pub fn new(value: f64) -> Result<Self, LegitimacyError> {
        if !value.is_finite() || value <= 0.0 {
            return Err(LegitimacyError::InvalidPositiveStrength { value });
        }

        Ok(Self(value))
    }

    #[tracing::instrument(skip(self))]
    pub fn value(self) -> f64 {
        self.0
    }
}

impl TryFrom<f64> for PositiveStrength {
    type Error = LegitimacyError;

    fn try_from(value: f64) -> Result<Self, Self::Error> {
        Self::new(value)
    }
}

impl From<PositiveStrength> for f64 {
    fn from(value: PositiveStrength) -> Self {
        value.value()
    }
}

impl PartialEq<f64> for PositiveStrength {
    fn eq(&self, other: &f64) -> bool {
        self.value() == *other
    }
}

impl PartialOrd<f64> for PositiveStrength {
    fn partial_cmp(&self, other: &f64) -> Option<std::cmp::Ordering> {
        self.value().partial_cmp(other)
    }
}

impl Sum<PositiveStrength> for f64 {
    fn sum<I: Iterator<Item = PositiveStrength>>(iter: I) -> Self {
        iter.map(PositiveStrength::value).sum()
    }
}

impl<'a> Sum<&'a PositiveStrength> for f64 {
    fn sum<I: Iterator<Item = &'a PositiveStrength>>(iter: I) -> Self {
        iter.map(|value| value.value()).sum()
    }
}

impl Div<f64> for PositiveStrength {
    type Output = f64;

    fn div(self, rhs: f64) -> Self::Output {
        self.value() / rhs
    }
}

impl Mul<f64> for PositiveStrength {
    type Output = f64;

    fn mul(self, rhs: f64) -> Self::Output {
        self.value() * rhs
    }
}

impl Sub<f64> for PositiveStrength {
    type Output = f64;

    fn sub(self, rhs: f64) -> Self::Output {
        self.value() - rhs
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, PartialOrd)]
#[serde(try_from = "f64", into = "f64")]
pub struct EstateTotal(f64);

impl EstateTotal {
    #[tracing::instrument(fields(value))]
    pub fn new(value: f64) -> Result<Self, LegitimacyError> {
        if !value.is_finite() || value <= 0.0 {
            return Err(LegitimacyError::InvalidEstateTotal { value });
        }

        Ok(Self(value))
    }

    #[tracing::instrument(skip(self))]
    pub fn value(self) -> f64 {
        self.0
    }

    #[tracing::instrument(skip(self), fields(scale))]
    pub fn scale(self, scale: f64) -> Result<Self, LegitimacyError> {
        Self::new(self.0 * scale)
    }
}

impl TryFrom<f64> for EstateTotal {
    type Error = LegitimacyError;

    fn try_from(value: f64) -> Result<Self, Self::Error> {
        Self::new(value)
    }
}

impl From<EstateTotal> for f64 {
    fn from(value: EstateTotal) -> Self {
        value.value()
    }
}

impl PartialEq<f64> for EstateTotal {
    fn eq(&self, other: &f64) -> bool {
        self.value() == *other
    }
}

impl Mul<f64> for EstateTotal {
    type Output = f64;

    fn mul(self, rhs: f64) -> Self::Output {
        self.value() * rhs
    }
}

impl Div<f64> for EstateTotal {
    type Output = f64;

    fn div(self, rhs: f64) -> Self::Output {
        self.value() / rhs
    }
}

impl Sub<f64> for EstateTotal {
    type Output = f64;

    fn sub(self, rhs: f64) -> Self::Output {
        self.value() - rhs
    }
}

/// The estate being allocated (autonomy tiers, compute budget, memory slots, etc.).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct Estate {
    pub total: EstateTotal,
    pub unit: String,
}

impl Estate {
    #[tracing::instrument(skip(unit), fields(total))]
    pub fn new(total: f64, unit: impl Into<String>) -> Result<Self, LegitimacyError> {
        Ok(Self {
            total: EstateTotal::new(total)?,
            unit: unit.into(),
        })
    }
}

/// A valid claim: a claimant's measured entitlement to a share of the estate.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct Claim {
    pub claimant_id: ClaimantId,
    pub strength: PositiveStrength,
    #[serde(default)]
    pub metrics: BTreeMap<String, f64>,
}

impl Claim {
    #[tracing::instrument(skip(claimant_id), fields(strength))]
    pub fn try_new(
        claimant_id: impl Into<ClaimantId>,
        strength: f64,
    ) -> Result<Self, LegitimacyError> {
        let claimant_id = claimant_id.into();
        validate_claimant_id(&claimant_id)?;
        validate_claim_strength(&claimant_id, strength)?;
        Ok(Self {
            claimant_id,
            strength: PositiveStrength::new(strength)?,
            metrics: BTreeMap::new(),
        })
    }

    #[tracing::instrument(skip(claimant_id), fields(strength))]
    pub fn new(claimant_id: impl Into<ClaimantId>, strength: f64) -> Result<Self, LegitimacyError> {
        Self::try_new(claimant_id, strength)
    }

    #[tracing::instrument(skip(self))]
    pub fn validate(&self) -> Result<(), LegitimacyError> {
        validate_claimant_id(&self.claimant_id)?;
        validate_claim_strength(&self.claimant_id, self.strength.value())
    }

    #[tracing::instrument(skip(claims))]
    pub fn validate_all(claims: &[Self]) -> Result<(), LegitimacyError> {
        let mut seen = BTreeSet::new();
        for claim in claims {
            claim.validate()?;
            if !seen.insert(claim.claimant_id.as_str()) {
                return Err(LegitimacyError::DuplicateClaimantId {
                    claimant_id: claim.claimant_id.clone(),
                });
            }
        }
        Ok(())
    }

    #[tracing::instrument(skip(self, name), fields(value))]
    pub fn with_metric(mut self, name: impl Into<String>, value: f64) -> Self {
        self.metrics.insert(name.into(), value);
        self
    }

    #[tracing::instrument(skip(self))]
    pub fn metric(&self, name: &str) -> f64 {
        match self.metrics.get(name) {
            Some(value) => *value,
            None => 0.0,
        }
    }
}

fn validate_claimant_id(claimant_id: &str) -> Result<(), LegitimacyError> {
    if claimant_id.trim().is_empty() {
        return Err(LegitimacyError::InvalidClaimantId {
            claimant_id: claimant_id.to_string(),
        });
    }

    Ok(())
}

fn validate_claim_strength(claimant_id: &str, strength: f64) -> Result<(), LegitimacyError> {
    if !strength.is_finite() || strength <= 0.0 {
        return Err(LegitimacyError::InvalidClaimStrength {
            claimant_id: claimant_id.to_string(),
            strength,
        });
    }

    Ok(())
}

pub(crate) fn validate_claims(claims: &[Claim], _context: &str) -> Result<(), LegitimacyError> {
    Claim::validate_all(claims)
}

/// An allocation: the rule's output — how the estate is divided.
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
#[serde(transparent)]
pub struct Allocation(BTreeMap<ClaimantId, f64>);

impl Allocation {
    #[tracing::instrument(skip(self, claims))]
    pub fn validate(&self, claims: &[Claim]) -> Result<(), LegitimacyError> {
        let expected_ids = claims
            .iter()
            .map(|claim| claim.claimant_id.as_str())
            .collect::<BTreeSet<_>>();

        for expected_id in &expected_ids {
            if !self.contains_key(*expected_id) {
                return Err(LegitimacyError::AllocationMissingClaimant {
                    claimant_id: (*expected_id).to_string(),
                });
            }
        }

        for (claimant_id, value) in self.iter() {
            if !value.is_finite() || *value < 0.0 {
                return Err(LegitimacyError::InvalidAllocationValue {
                    claimant_id: claimant_id.clone(),
                    value: *value,
                });
            }

            if !expected_ids.contains(claimant_id.as_str()) {
                return Err(LegitimacyError::AllocationUnknownClaimant {
                    claimant_id: claimant_id.clone(),
                });
            }
        }

        Ok(())
    }

    #[tracing::instrument(skip(self))]
    pub fn share_for(&self, claimant_id: &str, context: &str) -> Result<f64, LegitimacyError> {
        self.get(claimant_id).copied().ok_or_else(|| {
            LegitimacyError::missing_allocation_share(claimant_id.to_string(), context.to_string())
        })
    }

    #[tracing::instrument(skip(self, estate))]
    pub fn validate_feasible(&self, estate: &Estate) -> Result<(), LegitimacyError> {
        let total_allocated: f64 = self.values().sum();
        let estate_total = estate.total.value();
        let tolerance = EPSILON + EPSILON * (total_allocated.abs() + estate_total.abs());

        if total_allocated <= estate_total + tolerance {
            return Ok(());
        }

        Err(LegitimacyError::AllocationExceedsEstate {
            total_allocated,
            estate_total,
        })
    }

    #[tracing::instrument(skip(self, claims))]
    pub fn try_into_valid(self, claims: &[Claim]) -> Result<ValidAllocation, LegitimacyError> {
        self.validate(claims)?;
        Ok(ValidAllocation(self))
    }
}

impl Deref for Allocation {
    type Target = BTreeMap<ClaimantId, f64>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Allocation {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl From<BTreeMap<ClaimantId, f64>> for Allocation {
    fn from(value: BTreeMap<ClaimantId, f64>) -> Self {
        Self(value)
    }
}

impl FromIterator<(ClaimantId, f64)> for Allocation {
    fn from_iter<T: IntoIterator<Item = (ClaimantId, f64)>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl IntoIterator for Allocation {
    type Item = (ClaimantId, f64);
    type IntoIter = std::collections::btree_map::IntoIter<ClaimantId, f64>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a> IntoIterator for &'a Allocation {
    type Item = (&'a ClaimantId, &'a f64);
    type IntoIter = std::collections::btree_map::Iter<'a, ClaimantId, f64>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

/// A claimant-complete, non-negative allocation whose coverage has been validated.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(transparent)]
pub struct ValidAllocation(Allocation);

impl ValidAllocation {
    #[tracing::instrument(skip(allocation, claims))]
    pub fn new(allocation: Allocation, claims: &[Claim]) -> Result<Self, LegitimacyError> {
        allocation.try_into_valid(claims)
    }

    #[tracing::instrument(skip(self, estate))]
    pub fn validate_feasible(&self, estate: &Estate) -> Result<(), LegitimacyError> {
        self.0.validate_feasible(estate)
    }

    #[tracing::instrument(skip(self))]
    pub fn share_for(&self, claimant_id: &str, context: &str) -> Result<f64, LegitimacyError> {
        self.0.share_for(claimant_id, context)
    }

    #[tracing::instrument(skip(self))]
    pub fn into_inner(self) -> Allocation {
        self.0
    }
}

impl Deref for ValidAllocation {
    type Target = Allocation;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<ValidAllocation> for Allocation {
    fn from(value: ValidAllocation) -> Self {
        value.0
    }
}

pub(crate) fn evaluate_rule(
    rule: &Rule,
    claims: &[Claim],
    estate: &Estate,
    context: &str,
) -> Result<ValidAllocation, LegitimacyError> {
    validate_claims(claims, context)?;
    rule.allocate(claims, estate)
}

pub trait AllocateRule: Send + Sync {
    fn allocate(&self, claims: &[Claim], estate: &Estate) -> Result<Allocation, LegitimacyError>;
}

impl<F> AllocateRule for F
where
    F: Fn(&[Claim], &Estate) -> Result<Allocation, LegitimacyError> + Send + Sync + 'static,
{
    fn allocate(&self, claims: &[Claim], estate: &Estate) -> Result<Allocation, LegitimacyError> {
        self(claims, estate)
    }
}

#[tracing::instrument(skip(rule))]
pub fn allocator<F>(rule: F) -> Arc<dyn AllocateRule>
where
    F: AllocateRule + 'static,
{
    Arc::new(rule)
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum DeclarativeRuleKind {
    Proportional,
    /// A user-defined rule kind identified by name.
    ///
    /// Built-in allocators are registered in `rules.rs`; unknown names produce
    /// an error at allocation time rather than at parse time, so callers can
    /// construct and serialize `Custom` rules without coupling to any specific
    /// set of built-in names.
    Custom(String),
}

impl DeclarativeRuleKind {
    #[tracing::instrument]
    pub fn parse(kind: &str) -> Result<Self, LegitimacyError> {
        match kind {
            "proportional" => Ok(Self::Proportional),
            other => Ok(Self::Custom(other.to_string())),
        }
    }

    /// The string key that identifies this rule kind in policy files.
    pub fn as_str(&self) -> &str {
        match self {
            Self::Proportional => "proportional",
            Self::Custom(name) => name.as_str(),
        }
    }
}

/// Canonical rule payload used by both programmatic and declarative rules.
///
/// This is the anti-split-brain boundary: the compiler and axiom checkers only
/// evaluate rules through `RuleSpec::allocate`, so `*.rule.toml` policies and
/// programmatic closures share one write path.
#[derive(Clone)]
pub enum RuleSpec {
    Programmatic(Arc<dyn AllocateRule>),
    Declarative(DeclarativeRuleKind),
}

impl std::fmt::Debug for RuleSpec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Programmatic(_) => f.write_str("RuleSpec::Programmatic(..)"),
            Self::Declarative(kind) => f.debug_tuple("RuleSpec::Declarative").field(kind).finish(),
        }
    }
}

impl RuleSpec {
    #[tracing::instrument(skip(rule))]
    pub fn programmatic<F>(rule: F) -> Self
    where
        F: AllocateRule + 'static,
    {
        Self::Programmatic(allocator(rule))
    }

    #[tracing::instrument]
    pub fn declarative(kind: &str) -> Result<Self, LegitimacyError> {
        Ok(Self::Declarative(DeclarativeRuleKind::parse(kind)?))
    }

    #[tracing::instrument(skip(self, claims, estate))]
    pub fn allocate(
        &self,
        claims: &[Claim],
        estate: &Estate,
    ) -> Result<Allocation, LegitimacyError> {
        match self {
            Self::Programmatic(rule) => rule.allocate(claims, estate),
            Self::Declarative(DeclarativeRuleKind::Proportional) => {
                crate::rules::proportional_allocate(claims, estate)
            }
            Self::Declarative(DeclarativeRuleKind::Custom(name)) => {
                crate::rules::custom_allocate(name, claims, estate)
            }
        }
    }

    pub fn requires_feasible_allocation(&self) -> bool {
        match self {
            Self::Programmatic(_) | Self::Declarative(DeclarativeRuleKind::Proportional) => true,
            // Custom rules do not assert a feasibility guarantee by default;
            // they must opt in by registering a programmatic rule instead.
            Self::Declarative(DeclarativeRuleKind::Custom(_)) => false,
        }
    }
}

/// A governance rule: a function from (claims, estate) → allocation.
///
/// Rules are the object the legitimacy checker evaluates. A rule is admissible if it
/// satisfies consistency, solidarity, and monotonicity across the
/// declared perturbation family.
///
/// The `allocate` function is the rule itself. Everything else is metadata.
#[derive(Clone)]
pub struct Rule {
    pub name: String,
    pub version: String,
    /// Canonical rule payload: closures and parsed policies both flow through this enum.
    pub rule_spec: RuleSpec,
    /// Priority classes: claimants in the same class should be treated
    /// comparably under solidarity.
    pub priority_classes: Vec<String>,
}

impl Rule {
    #[tracing::instrument(skip(self, claims, estate), fields(rule_name = %self.name))]
    pub fn allocate(
        &self,
        claims: &[Claim],
        estate: &Estate,
    ) -> Result<ValidAllocation, LegitimacyError> {
        let allocation = self.rule_spec.allocate(claims, estate)?;
        let allocation = ValidAllocation::new(allocation, claims)?;
        if self.rule_spec.requires_feasible_allocation() {
            allocation.validate_feasible(estate)?;
        }
        Ok(allocation)
    }
}

impl AllocateRule for Rule {
    fn allocate(&self, claims: &[Claim], estate: &Estate) -> Result<Allocation, LegitimacyError> {
        Rule::allocate(self, claims, estate).map(Into::into)
    }
}

/// The result of an axiom check.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum Verdict {
    /// The rule satisfies this axiom across the tested perturbations.
    Admissible {
        axiom: String,
        perturbations_tested: usize,
    },
    /// The rule violates this axiom. Counterexample provided.
    Rejected {
        axiom: String,
        counterexample: Counterexample,
    },
}

/// A specific demonstration of an axiom violation.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct Counterexample {
    pub description: String,
    /// The original problem (claims + estate).
    pub original_claims: Vec<Claim>,
    pub original_estate: Estate,
    pub original_allocation: ValidAllocation,
    /// The perturbed problem.
    pub perturbed_claims: Vec<Claim>,
    pub perturbed_estate: Estate,
    pub perturbed_allocation: ValidAllocation,
    /// What went wrong.
    pub violation: String,
}

/// A compiled rule: proven admissible over its declared family.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompiledRule {
    pub name: String,
    pub version: String,
    pub axiom_verdicts: Vec<Verdict>,
    pub strategyproofness: StrategyproofnessVerdict,
    pub family_description: String,
    pub compiled_at: String,
}

impl CompiledRule {
    #[tracing::instrument(skip(self))]
    pub fn is_admissible(&self) -> bool {
        self.axiom_verdicts
            .iter()
            .all(|v| matches!(v, Verdict::Admissible { .. }))
            && matches!(
                self.strategyproofness,
                StrategyproofnessVerdict::Strategyproof
            )
    }

    #[tracing::instrument(skip(self))]
    pub fn content_hash(&self) -> Result<String, LegitimacyError> {
        let content = serde_json::to_vec(&serde_json::json!({
            "name": self.name,
            "version": self.version,
            "axiom_verdicts": self.axiom_verdicts,
            "strategyproofness": self.strategyproofness,
            "family_description": self.family_description,
            "compiled_at": self.compiled_at,
        }))
        .map_err(|source| LegitimacyError::Serialize {
            context: "compiled rule content hash".to_string(),
            source,
        })?;
        let digest = Sha256::digest(&content);
        Ok(hex_encode(&digest))
    }

    #[tracing::instrument(skip(self))]
    pub fn violations(&self) -> Vec<&Counterexample> {
        self.axiom_verdicts
            .iter()
            .filter_map(|v| match v {
                Verdict::Rejected { counterexample, .. } => Some(counterexample),
                _ => None,
            })
            .collect()
    }
}

/// A promotion certificate: proof that a specific act was governed by
/// an admissible rule with checkable evidence.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Certificate {
    pub rule_name: String,
    pub rule_version: String,
    #[serde(default)]
    pub compiled_rule_hash: String,
    pub act_description: String,
    pub claimant_id: ClaimantId,
    pub outcome: f64,
    pub evidence: BTreeMap<String, String>,
    pub issued_at: String,
    pub admissible: bool,
}

fn hex_encode(bytes: &[u8]) -> String {
    let mut encoded = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write as _;
        let _ = write!(&mut encoded, "{byte:02x}");
    }
    encoded
}

/// Declared perturbation parameters for compiler checks.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct Family {
    /// Whether the declared family includes all single-claimant reductions.
    pub reductions: bool,
    /// Estate shock scale factors used for solidarity checks.
    pub shocks: Vec<f64>,
    /// Claim-strength deltas used for monotonicity checks.
    pub strengthening_deltas: Vec<PositiveStrength>,
    /// Invert the monotonicity check direction.
    ///
    /// When `true`, the checker enforces that strengthening a claim never
    /// *increases* its allocation — the contract for safety-clearance rules
    /// where higher strength signals greater risk. Defaults to `false`.
    #[serde(default)]
    pub monotonicity_inversion: bool,
}

impl Family {
    #[tracing::instrument(skip(self))]
    pub fn describe(&self) -> String {
        format!(
            "reductions={}, shocks={:?}, strengthening_deltas={:?}, monotonicity_inversion={}",
            self.reductions,
            self.shocks,
            self.strengthening_deltas
                .iter()
                .map(|delta| delta.value())
                .collect::<Vec<_>>(),
            self.monotonicity_inversion
        )
    }
}

/// A rejection report: one or more axiom violations found during compilation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RejectionReport {
    pub rule_name: String,
    pub rule_version: String,
    pub axiom_verdicts: Vec<Verdict>,
    pub rejected_at: String,
}

impl RejectionReport {
    #[tracing::instrument(skip(self))]
    pub fn violations(&self) -> Vec<&Counterexample> {
        self.axiom_verdicts
            .iter()
            .filter_map(|v| match v {
                Verdict::Rejected { counterexample, .. } => Some(counterexample),
                _ => None,
            })
            .collect()
    }
}

/// The result of the legitimacy compiler.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CompileResult {
    /// All three axioms pass over the declared family.
    Admissible(CompiledRule),
    /// One or more axiom violations found. Counterexamples included.
    Rejected(RejectionReport),
}

impl CompileResult {
    #[tracing::instrument(skip(self))]
    pub fn is_admissible(&self) -> bool {
        matches!(self, Self::Admissible(_))
    }

    #[tracing::instrument(skip(self))]
    pub fn violations(&self) -> Vec<&Counterexample> {
        match self {
            Self::Admissible(_) => vec![],
            Self::Rejected(r) => r.violations(),
        }
    }
}
