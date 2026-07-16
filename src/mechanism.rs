use crate::{
    Claim, ClaimantId, Decision, EPSILON, Estate, GovernanceClaim, GovernanceGraph, GovernanceNode,
    LegitimacyError, Rule, ValidAllocation, evaluate_rule,
    graph::{
        node::{ClaimDecision, decision_rank, evaluate_node},
        traverse,
    },
};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

const MISREPORT_FACTORS: [f64; 5] = [0.5, 0.8, 1.2, 1.5, 2.0];
const STRATEGYPROOF_CONTEXT: &str = "strategyproofness baseline";
const MANIPULATION_CONTEXT: &str = "strategyproofness misreport";

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct StrategyproofnessWitness {
    pub claimant: ClaimantId,
    pub true_strength: f64,
    pub reported: f64,
    pub true_alloc: f64,
    pub manipulated_alloc: f64,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum StrategyproofnessVerdict {
    Strategyproof,
    Manipulable {
        claimant: ClaimantId,
        true_strength: f64,
        reported: f64,
        true_alloc: f64,
        manipulated_alloc: f64,
    },
}

impl StrategyproofnessVerdict {
    pub fn manipulable(witness: StrategyproofnessWitness) -> Self {
        Self::Manipulable {
            claimant: witness.claimant,
            true_strength: witness.true_strength,
            reported: witness.reported,
            true_alloc: witness.true_alloc,
            manipulated_alloc: witness.manipulated_alloc,
        }
    }
}

pub trait StrategyproofnessOutcome {
    fn strategyproofness_witness(&self) -> Option<StrategyproofnessWitness>;

    fn strategyproofness_exposure(&self) -> f64 {
        if self.strategyproofness_witness().is_some() {
            1.0
        } else {
            0.0
        }
    }
}

impl StrategyproofnessOutcome for StrategyproofnessVerdict {
    fn strategyproofness_witness(&self) -> Option<StrategyproofnessWitness> {
        match self {
            Self::Strategyproof => None,
            Self::Manipulable {
                claimant,
                true_strength,
                reported,
                true_alloc,
                manipulated_alloc,
            } => Some(StrategyproofnessWitness {
                claimant: claimant.clone(),
                true_strength: *true_strength,
                reported: *reported,
                true_alloc: *true_alloc,
                manipulated_alloc: *manipulated_alloc,
            }),
        }
    }
}

pub fn check_strategyproofness(
    rule: &Rule,
    claims: &[Claim],
    estate: &Estate,
) -> Result<StrategyproofnessVerdict, LegitimacyError> {
    let baseline = evaluate_rule(rule, claims, estate, STRATEGYPROOF_CONTEXT)?;
    check_reported_strength_manipulations(
        claims,
        allocation_scores(&baseline),
        |candidate_claims| {
            let manipulated = evaluate_rule(rule, candidate_claims, estate, MANIPULATION_CONTEXT)?;
            Ok(allocation_scores(&manipulated))
        },
    )
}

pub fn check_binary_strategyproofness(
    node: &GovernanceNode,
    claims: &[GovernanceClaim],
) -> Result<StrategyproofnessVerdict, LegitimacyError> {
    let baseline = evaluate_node(node, claims)?;
    check_reported_strength_manipulations(claims, decision_scores(&baseline), |candidate_claims| {
        let manipulated = evaluate_node(node, candidate_claims)?;
        Ok(decision_scores(&manipulated))
    })
}

pub fn check_graph_strategyproofness_verdict(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
) -> Result<StrategyproofnessVerdict, LegitimacyError> {
    let baseline = traverse(graph, claims)?.final_decisions;
    check_reported_strength_manipulations(
        claims,
        final_decision_scores(&baseline),
        |candidate_claims| {
            let manipulated = traverse(graph, candidate_claims)?.final_decisions;
            Ok(final_decision_scores(&manipulated))
        },
    )
}

trait StrategyproofnessClaim: Clone {
    fn claimant_id(&self) -> &ClaimantId;
    fn strength_value(&self) -> f64;
    fn with_reported_strength(&self, reported: f64) -> Result<Self, LegitimacyError>;
}

impl StrategyproofnessClaim for Claim {
    fn claimant_id(&self) -> &ClaimantId {
        &self.claimant_id
    }

    fn strength_value(&self) -> f64 {
        self.strength.value()
    }

    fn with_reported_strength(&self, reported: f64) -> Result<Self, LegitimacyError> {
        Ok(Self {
            claimant_id: self.claimant_id.clone(),
            strength: reported.try_into()?,
            metrics: self.metrics.clone(),
        })
    }
}

impl StrategyproofnessClaim for GovernanceClaim {
    fn claimant_id(&self) -> &ClaimantId {
        &self.claimant_id
    }

    fn strength_value(&self) -> f64 {
        self.strength
    }

    fn with_reported_strength(&self, reported: f64) -> Result<Self, LegitimacyError> {
        let mut updated = self.clone();
        updated.strength = reported;
        Ok(updated)
    }
}

fn check_reported_strength_manipulations<C, E>(
    claims: &[C],
    baseline_scores: BTreeMap<ClaimantId, f64>,
    mut evaluate_scores: E,
) -> Result<StrategyproofnessVerdict, LegitimacyError>
where
    C: StrategyproofnessClaim,
    E: FnMut(&[C]) -> Result<BTreeMap<ClaimantId, f64>, LegitimacyError>,
{
    for (index, claim) in claims.iter().enumerate() {
        let true_alloc = score_for(&baseline_scores, claim.claimant_id(), STRATEGYPROOF_CONTEXT)?;
        for factor in MISREPORT_FACTORS {
            let reported = claim.strength_value() * factor;
            let manipulated_claims = claims
                .iter()
                .enumerate()
                .map(|(candidate_index, candidate)| {
                    if candidate_index == index {
                        candidate.with_reported_strength(reported)
                    } else {
                        Ok(candidate.clone())
                    }
                })
                .collect::<Result<Vec<_>, LegitimacyError>>()?;
            let manipulated_scores = evaluate_scores(&manipulated_claims)?;
            let manipulated_alloc = score_for(
                &manipulated_scores,
                claim.claimant_id(),
                MANIPULATION_CONTEXT,
            )?;

            if strictly_improves(manipulated_alloc, true_alloc) {
                return Ok(StrategyproofnessVerdict::manipulable(
                    StrategyproofnessWitness {
                        claimant: claim.claimant_id().clone(),
                        true_strength: claim.strength_value(),
                        reported,
                        true_alloc,
                        manipulated_alloc,
                    },
                ));
            }
        }
    }

    Ok(StrategyproofnessVerdict::Strategyproof)
}

fn allocation_scores(allocation: &ValidAllocation) -> BTreeMap<ClaimantId, f64> {
    allocation
        .iter()
        .map(|(claimant_id, share)| (claimant_id.clone(), *share))
        .collect()
}

fn decision_scores(decisions: &[ClaimDecision]) -> BTreeMap<ClaimantId, f64> {
    decisions
        .iter()
        .map(|decision| {
            (
                decision.claimant_id.clone(),
                f64::from(decision_rank(&decision.decision)),
            )
        })
        .collect()
}

fn final_decision_scores(decisions: &BTreeMap<ClaimantId, Decision>) -> BTreeMap<ClaimantId, f64> {
    decisions
        .iter()
        .map(|(claimant_id, decision)| (claimant_id.clone(), f64::from(decision_rank(decision))))
        .collect()
}

fn score_for(
    scores: &BTreeMap<ClaimantId, f64>,
    claimant_id: &str,
    context: &str,
) -> Result<f64, LegitimacyError> {
    scores
        .get(claimant_id)
        .copied()
        .ok_or_else(|| LegitimacyError::missing_allocation_share(claimant_id.to_string(), context))
}

fn strictly_improves(candidate: f64, baseline: f64) -> bool {
    let tolerance = EPSILON + EPSILON * (candidate.abs() + baseline.abs());
    candidate > baseline + tolerance
}
