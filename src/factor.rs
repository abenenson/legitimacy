use crate::{
    Claim, Claimant, Estate, Family, LegitimacyError, PositiveStrength, Rule,
    axioms::diagnostics::{
        consistency::{FullConsistencyOptions, check_full_consistency},
        monotonicity::check_monotonicity,
        solidarity::check_solidarity,
        strategyproofness::{StrategyproofnessOutcome, check_strategyproofness},
    },
};
use serde::{Deserialize, Serialize};

const DEFAULT_SHOCKS: [f64; 4] = [0.5, 0.75, 1.25, 1.5];
const DEFAULT_STRENGTHENING: [f64; 3] = [0.1, 0.5, 1.0];
const RADAR_WIDTH: usize = 10;

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq)]
pub struct GovernanceFactorExposure {
    pub consistency: f64,
    pub solidarity: f64,
    pub monotonicity: f64,
    pub strategyproofness: f64,
    pub nonvacuity: f64,
}

impl GovernanceFactorExposure {
    pub fn render_text_radar(&self) -> String {
        let row =
            |name: &str, value: f64| format!("  {:<18} {:.2}  {}", name, value, radar_axis(value));
        [
            "Governance Factor Exposure".to_string(),
            row("consistency", self.consistency),
            row("solidarity", self.solidarity),
            row("monotonicity", self.monotonicity),
            row("strategyproofness", self.strategyproofness),
            row("nonvacuity", self.nonvacuity),
        ]
        .join("\n")
    }
}

pub fn compute_factor_exposure(
    rule: &Rule,
    claims: &[Claim],
    estate: &Estate,
) -> Result<GovernanceFactorExposure, LegitimacyError> {
    let claimants = default_claimants(rule, claims);
    let family = default_family()?;
    compute_factor_exposure_with_family(rule, claims, &claimants, estate, &family)
}

pub fn compute_factor_exposure_with_family(
    rule: &Rule,
    claims: &[Claim],
    claimants: &[Claimant],
    estate: &Estate,
    family: &Family,
) -> Result<GovernanceFactorExposure, LegitimacyError> {
    compute_factor_exposure_with_family_and_options(
        rule,
        claims,
        claimants,
        estate,
        family,
        FullConsistencyOptions::default(),
    )
}

pub fn compute_factor_exposure_with_family_and_options(
    rule: &Rule,
    claims: &[Claim],
    claimants: &[Claimant],
    estate: &Estate,
    family: &Family,
    consistency_options: FullConsistencyOptions,
) -> Result<GovernanceFactorExposure, LegitimacyError> {
    let consistency = if matches!(
        check_full_consistency(rule, claims, estate, consistency_options)?,
        crate::Verdict::Rejected { .. }
    ) {
        1.0
    } else {
        0.0
    };

    let solidarity = if matches!(
        check_solidarity(rule, claims, estate, claimants, &family.shocks)?,
        crate::Verdict::Rejected { .. }
    ) {
        1.0
    } else {
        0.0
    };

    let monotonicity = if matches!(
        check_monotonicity(
            rule,
            claims,
            estate,
            &family.strengthening_deltas,
            family.monotonicity_inversion,
        )?,
        crate::Verdict::Rejected { .. }
    ) {
        1.0
    } else {
        0.0
    };

    let strategyproofness =
        check_strategyproofness(rule, claims, estate)?.strategyproofness_exposure();

    let allocation = rule.allocate(claims, estate)?.into_inner();
    let nonvacuity =
        if claims.is_empty() || !allocation.values().any(|share| *share > crate::EPSILON) {
            1.0
        } else {
            0.0
        };

    Ok(GovernanceFactorExposure {
        consistency,
        solidarity,
        monotonicity,
        strategyproofness,
        nonvacuity,
    })
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

fn radar_axis(exposure: f64) -> String {
    let clamped = exposure.clamp(0.0, 1.0);
    let filled = (clamped * RADAR_WIDTH as f64).round() as usize;
    let hashes = "#".repeat(filled);
    let dots = ".".repeat(RADAR_WIDTH.saturating_sub(filled));
    format!("[{hashes}{dots}]")
}
