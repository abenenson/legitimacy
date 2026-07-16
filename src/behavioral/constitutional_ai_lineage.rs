use legitimacy::spectral::positive_procedure::{
    BinaryDecision, CapacityGraph, CapacityKernel, ExactCapacityCalibration, FixedCvGraph,
    PositiveProcedureCertificate, PreservedDiagnostic, governance_certificate,
};

const EPSILON: f64 = 1e-9;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConstitutionalAIDecision {
    Permit,
    Escalate,
    Deny,
}

impl ConstitutionalAIDecision {
    pub fn to_binary(self) -> BinaryDecision {
        match self {
            Self::Permit => BinaryDecision::Permit,
            Self::Escalate | Self::Deny => BinaryDecision::Deny,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConstitutionalAIClaimClass {
    HarmCategorical,
    Benign,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ConstitutionalAIBehavioralLineage<G = FixedCvGraph> {
    pub graph: G,
    pub signal: Vec<f64>,
    pub claim_classes: Vec<ConstitutionalAIClaimClass>,
    pub policy: Vec<ConstitutionalAIDecision>,
}

impl<G> ConstitutionalAIBehavioralLineage<G> {
    pub fn new(
        graph: G,
        signal: Vec<f64>,
        claim_classes: Vec<ConstitutionalAIClaimClass>,
        policy: Vec<ConstitutionalAIDecision>,
    ) -> Result<Self, ConstitutionalAILineageError> {
        if claim_classes.is_empty() || claim_classes.len() != policy.len() {
            return Err(ConstitutionalAILineageError::ShapeMismatch {
                claim_classes: claim_classes.len(),
                policy: policy.len(),
            });
        }
        Ok(Self {
            graph,
            signal,
            claim_classes,
            policy,
        })
    }

    pub fn is_trained_audit_subject(&self) -> bool {
        self.claim_classes
            .iter()
            .zip(self.policy.iter())
            .all(|(class, decision)| match class {
                ConstitutionalAIClaimClass::HarmCategorical => {
                    matches!(
                        decision,
                        ConstitutionalAIDecision::Escalate | ConstitutionalAIDecision::Deny
                    )
                }
                ConstitutionalAIClaimClass::Benign => *decision == ConstitutionalAIDecision::Permit,
            })
    }

    pub fn deployment_binary_decision(&self, state: usize) -> Option<BinaryDecision> {
        self.policy.get(state).map(|decision| decision.to_binary())
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ConstitutionalAICapacityLineage<G = FixedCvGraph> {
    pub lineage: ConstitutionalAIBehavioralLineage<G>,
    pub delta: f64,
    pub audit_amplitude_budget: f64,
}

impl<G> ConstitutionalAICapacityLineage<G>
where
    G: CapacityGraph + Clone,
{
    pub fn new(
        lineage: ConstitutionalAIBehavioralLineage<G>,
        delta: f64,
        audit_amplitude_budget: f64,
    ) -> Result<Self, ConstitutionalAILineageError> {
        if !(delta.is_finite() && delta > 0.0) {
            return Err(ConstitutionalAILineageError::NonPositiveDelta(delta));
        }
        if !(audit_amplitude_budget.is_finite() && audit_amplitude_budget > 0.0) {
            return Err(
                ConstitutionalAILineageError::NonPositiveAuditAmplitudeBudget(
                    audit_amplitude_budget,
                ),
            );
        }
        let cv = lineage.graph.cv(&lineage.signal);
        if !(cv.is_finite() && cv > 0.0) {
            return Err(ConstitutionalAILineageError::NonPositiveCv(cv));
        }
        Ok(Self {
            lineage,
            delta,
            audit_amplitude_budget,
        })
    }

    pub fn capability_response(&self, c: f64) -> BinaryDecision {
        self.lineage
            .graph
            .capability_response(&self.lineage.signal, self.delta, c)
    }

    pub fn c_star(&self) -> f64 {
        self.lineage.graph.c_star(&self.lineage.signal, self.delta)
    }

    pub fn sp_violation(&self, gamma: f64) -> bool {
        self.lineage.graph.sp_violation(&self.lineage.signal, gamma)
    }

    pub fn to_capacity_kernel(
        &self,
        channel: ExactCapacityCalibration,
    ) -> CapacityKernel<G, Vec<f64>, ExactCapacityCalibration> {
        CapacityKernel {
            graph: self.lineage.graph.clone(),
            signal: self.lineage.signal.clone(),
            delta: self.delta,
            channel,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConstitutionalAISubstrateFailureMode {
    HarmCategoryLeakPath,
    OverEscalationFalsePositiveResidual,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConstitutionalAISubstrateVerdict {
    Admissible,
    RejectWithFailureMode(ConstitutionalAISubstrateFailureMode),
}

#[derive(Clone, Debug, PartialEq)]
pub enum ConstitutionalAILineageError {
    ShapeMismatch { claim_classes: usize, policy: usize },
    NonPositiveDelta(f64),
    NonPositiveCv(f64),
    NonPositiveAuditAmplitudeBudget(f64),
    MissingState(usize),
}

pub fn profile_sensitive_policy_label<G>(
    left: &ConstitutionalAICapacityLineage<G>,
    right: &ConstitutionalAICapacityLineage<G>,
    state: usize,
) -> Result<bool, ConstitutionalAILineageError> {
    let left_policy = left
        .lineage
        .policy
        .get(state)
        .ok_or(ConstitutionalAILineageError::MissingState(state))?;
    let right_policy = right
        .lineage
        .policy
        .get(state)
        .ok_or(ConstitutionalAILineageError::MissingState(state))?;
    Ok(left_policy != right_policy)
}

pub fn cai_harm_categorical_policy_denies<G>(
    lineage: &ConstitutionalAICapacityLineage<G>,
    state: usize,
) -> Result<bool, ConstitutionalAILineageError> {
    let class = lineage
        .lineage
        .claim_classes
        .get(state)
        .ok_or(ConstitutionalAILineageError::MissingState(state))?;
    let decision = lineage
        .lineage
        .deployment_binary_decision(state)
        .ok_or(ConstitutionalAILineageError::MissingState(state))?;
    Ok(*class == ConstitutionalAIClaimClass::HarmCategorical && decision == BinaryDecision::Deny)
}

pub fn cai_capability_boundary_benign_response_matches_c_star<G>(
    lineage: &ConstitutionalAICapacityLineage<G>,
    state: usize,
    c: f64,
) -> Result<bool, ConstitutionalAILineageError>
where
    G: CapacityGraph + Clone,
{
    let class = lineage
        .lineage
        .claim_classes
        .get(state)
        .ok_or(ConstitutionalAILineageError::MissingState(state))?;
    let policy = lineage
        .lineage
        .deployment_binary_decision(state)
        .ok_or(ConstitutionalAILineageError::MissingState(state))?;
    if *class != ConstitutionalAIClaimClass::Benign || !(c.is_finite() && c > 0.0) {
        return Ok(false);
    }

    let response_matches_policy = lineage.capability_response(c) == policy;
    let at_or_above_boundary = lineage.c_star() <= c + EPSILON;
    Ok(response_matches_policy == at_or_above_boundary)
}

pub fn benign_boundary_policy_matches<G>(lineage: &ConstitutionalAICapacityLineage<G>) -> bool
where
    G: CapacityGraph + Clone,
{
    let c_star = lineage.c_star();
    lineage
        .lineage
        .claim_classes
        .iter()
        .enumerate()
        .filter(|(_, class)| **class == ConstitutionalAIClaimClass::Benign)
        .all(|(state, _)| {
            cai_capability_boundary_benign_response_matches_c_star(lineage, state, c_star)
                .unwrap_or(false)
        })
}

pub fn constant_deny_policy(state_count: usize) -> Vec<ConstitutionalAIDecision> {
    vec![ConstitutionalAIDecision::Deny; state_count]
}

pub fn substrate_verdict_for_policy(
    claim_classes: &[ConstitutionalAIClaimClass],
    policy: &[ConstitutionalAIDecision],
    certificate: &PositiveProcedureCertificate,
) -> ConstitutionalAISubstrateVerdict {
    let harm_permit = claim_classes
        .iter()
        .zip(policy.iter())
        .any(|(class, decision)| {
            *class == ConstitutionalAIClaimClass::HarmCategorical
                && decision.to_binary() == BinaryDecision::Permit
        });
    if harm_permit {
        return ConstitutionalAISubstrateVerdict::RejectWithFailureMode(
            ConstitutionalAISubstrateFailureMode::HarmCategoryLeakPath,
        );
    }

    let benign_deny = claim_classes
        .iter()
        .zip(policy.iter())
        .any(|(class, decision)| {
            *class == ConstitutionalAIClaimClass::Benign
                && decision.to_binary() == BinaryDecision::Deny
        });
    if certificate.kind() == PreservedDiagnostic::Monotonicity && benign_deny {
        return ConstitutionalAISubstrateVerdict::RejectWithFailureMode(
            ConstitutionalAISubstrateFailureMode::OverEscalationFalsePositiveResidual,
        );
    }

    ConstitutionalAISubstrateVerdict::Admissible
}

pub fn substrate_verdict<G>(
    lineage: &ConstitutionalAICapacityLineage<G>,
    certificate: &PositiveProcedureCertificate,
) -> ConstitutionalAISubstrateVerdict {
    substrate_verdict_for_policy(
        &lineage.lineage.claim_classes,
        &lineage.lineage.policy,
        certificate,
    )
}

pub trait ConstitutionalAIPositiveProcedureCarrier<G>
where
    G: CapacityGraph + Clone,
{
    fn lineage(&self) -> &ConstitutionalAICapacityLineage<G>;

    fn consistency_from_harm_denial(&self) -> bool {
        self.lineage()
            .lineage
            .claim_classes
            .iter()
            .enumerate()
            .filter(|(_, class)| **class == ConstitutionalAIClaimClass::HarmCategorical)
            .all(|(state, _)| {
                cai_harm_categorical_policy_denies(self.lineage(), state).unwrap_or(false)
            })
    }

    fn monotonicity_from_benign_boundary(&self) -> bool {
        benign_boundary_policy_matches(self.lineage())
    }
}

#[derive(Clone, Debug)]
pub struct StructuralConstitutionalAIPositiveProcedureCarrier<G = FixedCvGraph>
where
    G: CapacityGraph + Clone,
{
    pub lineage: ConstitutionalAICapacityLineage<G>,
}

impl<G> ConstitutionalAIPositiveProcedureCarrier<G>
    for StructuralConstitutionalAIPositiveProcedureCarrier<G>
where
    G: CapacityGraph + Clone,
{
    fn lineage(&self) -> &ConstitutionalAICapacityLineage<G> {
        &self.lineage
    }
}

pub fn constitutional_ai_witness_claim_classes5() -> Vec<ConstitutionalAIClaimClass> {
    let mut classes = vec![ConstitutionalAIClaimClass::Benign; 5];
    classes[0] = ConstitutionalAIClaimClass::HarmCategorical;
    classes
}

pub fn constitutional_ai_witness_policy5() -> Vec<ConstitutionalAIDecision> {
    let mut policy = vec![ConstitutionalAIDecision::Permit; 5];
    policy[0] = ConstitutionalAIDecision::Deny;
    policy
}

pub fn constitutional_ai_witness_lineage5()
-> Result<ConstitutionalAIBehavioralLineage, ConstitutionalAILineageError> {
    ConstitutionalAIBehavioralLineage::new(
        FixedCvGraph { cv: 0.75 },
        vec![0.0, 0.25, 0.5, 0.75, 1.0],
        constitutional_ai_witness_claim_classes5(),
        constitutional_ai_witness_policy5(),
    )
}

pub fn constitutional_ai_capacity_witness_lineage()
-> Result<ConstitutionalAICapacityLineage, ConstitutionalAILineageError> {
    ConstitutionalAICapacityLineage::new(constitutional_ai_witness_lineage5()?, 0.1, 2.0 / 15.0)
}

pub fn constitutional_ai_witness_positive_procedure_kernel5()
-> CapacityKernel<FixedCvGraph, Vec<f64>, ExactCapacityCalibration> {
    CapacityKernel {
        graph: FixedCvGraph { cv: 0.375 },
        signal: vec![0.0, 0.125, 0.25, 0.375, 0.5],
        delta: 0.1,
        channel: ExactCapacityCalibration { capacity: 0.375 },
    }
}

pub fn constitutional_ai_witness_positive_procedure_certificate5_consistency()
-> PositiveProcedureCertificate {
    // SAFETY: the witness kernel has delta 0.1, cv/capacity 0.375, and this
    // subcritical scale is positive and below c_star = 4/15.
    governance_certificate(&constitutional_ai_witness_positive_procedure_kernel5(), 0.1).unwrap()
}

pub fn constitutional_ai_witness_positive_procedure_certificate5_boundary()
-> PositiveProcedureCertificate {
    // SAFETY: the witness kernel has matching positive cv/capacity 0.375 and
    // scale 4/15 equals c_star for delta 0.1.
    governance_certificate(
        &constitutional_ai_witness_positive_procedure_kernel5(),
        4.0 / 15.0,
    )
    .unwrap()
}

pub fn constitutional_ai_witness_permits_harm_policy5() -> Vec<ConstitutionalAIDecision> {
    vec![ConstitutionalAIDecision::Permit; 5]
}

pub fn constitutional_ai_witness_denies_benign_policy5() -> Vec<ConstitutionalAIDecision> {
    vec![ConstitutionalAIDecision::Deny; 5]
}

#[cfg(test)]
mod tests {
    use super::{
        ConstitutionalAISubstrateFailureMode, ConstitutionalAISubstrateVerdict,
        benign_boundary_policy_matches, cai_capability_boundary_benign_response_matches_c_star,
        cai_harm_categorical_policy_denies, constant_deny_policy,
        constitutional_ai_capacity_witness_lineage, constitutional_ai_witness_claim_classes5,
        constitutional_ai_witness_denies_benign_policy5,
        constitutional_ai_witness_permits_harm_policy5,
        constitutional_ai_witness_positive_procedure_certificate5_boundary,
        profile_sensitive_policy_label, substrate_verdict, substrate_verdict_for_policy,
    };

    #[test]
    fn harm_categorical_permit_policy_rejects_with_leak_path() {
        let certificate = constitutional_ai_witness_positive_procedure_certificate5_boundary();
        let verdict = substrate_verdict_for_policy(
            &constitutional_ai_witness_claim_classes5(),
            &constitutional_ai_witness_permits_harm_policy5(),
            &certificate,
        );

        assert_eq!(
            verdict,
            ConstitutionalAISubstrateVerdict::RejectWithFailureMode(
                ConstitutionalAISubstrateFailureMode::HarmCategoryLeakPath
            )
        );
    }

    #[test]
    fn benign_permits_at_boundary_for_trained_witness() {
        let lineage = constitutional_ai_capacity_witness_lineage().unwrap();
        let c_star = lineage.c_star();

        assert!(cai_harm_categorical_policy_denies(&lineage, 0).unwrap());
        assert!(
            cai_capability_boundary_benign_response_matches_c_star(&lineage, 1, c_star).unwrap()
        );
        assert!(benign_boundary_policy_matches(&lineage));
        assert_eq!(
            substrate_verdict(
                &lineage,
                &constitutional_ai_witness_positive_procedure_certificate5_boundary()
            ),
            ConstitutionalAISubstrateVerdict::Admissible
        );
    }

    #[test]
    fn profile_sensitivity_excludes_constant_deny() {
        let witness = constitutional_ai_capacity_witness_lineage().unwrap();
        let mut constant = witness.clone();
        constant.lineage.policy = constant_deny_policy(5);

        assert!(profile_sensitive_policy_label(&witness, &constant, 1).unwrap());
        assert!(!benign_boundary_policy_matches(&constant));

        let verdict = substrate_verdict_for_policy(
            &constant.lineage.claim_classes,
            &constitutional_ai_witness_denies_benign_policy5(),
            &constitutional_ai_witness_positive_procedure_certificate5_boundary(),
        );
        assert_eq!(
            verdict,
            ConstitutionalAISubstrateVerdict::RejectWithFailureMode(
                ConstitutionalAISubstrateFailureMode::OverEscalationFalsePositiveResidual
            )
        );
    }
}
