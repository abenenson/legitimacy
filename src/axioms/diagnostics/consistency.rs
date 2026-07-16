//! Consistency axiom: a rule's verdict on any subproblem should match
//! its verdict when that subproblem is embedded in a larger context.
//!
//! Formally (Young 1994): if we remove any subset of claimants and reduce the
//! estate by their combined share, the rule applied to the resulting
//! sub-problem should reproduce the original allocations for all remaining
//! claimants.
//!
//! The public checker defaults to Young's full sub-coalition consistency.
//! Bounded consistency is still available as an explicitly labeled diagnostic
//! mode for operational probes that cannot afford exponential enumeration.

use crate::{
    Claim, Counterexample, EPSILON, Estate, LegitimacyError, Rule, ValidAllocation, Verdict,
    evaluate_rule,
};
use num_rational::Ratio;
use std::collections::BTreeMap;

const FULL_CONSISTENCY_WARN_CLAIMANTS: usize = 20;

/// Consistency enumeration mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConsistencyMode {
    /// Enumerate every non-empty proper removed coalition.
    Full,
    /// Enumerate removed coalitions with cardinality at most `max_removed`.
    Bounded { max_removed: usize },
}

/// Options for Young consistency checking.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FullConsistencyOptions {
    pub mode: ConsistencyMode,
    pub allow_exponential_consistency: bool,
}

/// Complexity counters from a consistency run.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ConsistencyComplexity {
    pub coalitions_tested: usize,
    pub survivor_checks: usize,
}

/// Verdict plus complexity metadata for callers that need structured audit data.
#[derive(Debug, Clone, PartialEq)]
pub struct FullConsistencyAudit {
    pub verdict: Verdict,
    pub complexity: ConsistencyComplexity,
}

pub type ConsistencyRational = Ratio<i64>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RationalClaim {
    pub claimant_id: String,
    pub strength: ConsistencyRational,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RationalEstate {
    pub total: ConsistencyRational,
    pub unit: String,
}

pub type RationalAllocation = BTreeMap<String, ConsistencyRational>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RationalFullConsistencyVerdict {
    Admissible,
    Rejected(RationalConsistencyCounterexample),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RationalConsistencyCounterexample {
    pub removed: Vec<String>,
    pub survivor: String,
    pub original_share: ConsistencyRational,
    pub reduced_share: ConsistencyRational,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RationalFullConsistencyAuditArtifact {
    pub verdict: RationalFullConsistencyVerdict,
    pub complexity: ConsistencyComplexity,
}

impl RationalClaim {
    pub fn new(
        claimant_id: impl Into<String>,
        strength: ConsistencyRational,
    ) -> Result<Self, LegitimacyError> {
        if strength <= ConsistencyRational::from_integer(0) {
            return Err(LegitimacyError::invalid_input(
                "rational claim strength must be positive",
            ));
        }
        Ok(Self {
            claimant_id: claimant_id.into(),
            strength,
        })
    }
}

impl RationalEstate {
    pub fn new(
        total: ConsistencyRational,
        unit: impl Into<String>,
    ) -> Result<Self, LegitimacyError> {
        if total <= ConsistencyRational::from_integer(0) {
            return Err(LegitimacyError::invalid_input(
                "rational estate total must be positive",
            ));
        }
        Ok(Self {
            total,
            unit: unit.into(),
        })
    }
}

impl Default for FullConsistencyOptions {
    fn default() -> Self {
        Self {
            mode: ConsistencyMode::Full,
            allow_exponential_consistency: false,
        }
    }
}

/// Check full Young consistency unless `options.mode` explicitly requests a
/// bounded approximation.
#[tracing::instrument(
    skip(rule, claims, estate),
    fields(axiom_name = "consistency", result = tracing::field::Empty)
)]
pub fn check_full_consistency(
    rule: &Rule,
    claims: &[Claim],
    estate: &Estate,
    options: FullConsistencyOptions,
) -> Result<Verdict, LegitimacyError> {
    Ok(check_full_consistency_audit(rule, claims, estate, options)?.verdict)
}

/// Check consistency and return structured complexity metadata.
#[tracing::instrument(
    skip(rule, claims, estate),
    fields(
        axiom_name = "consistency",
        result = tracing::field::Empty,
        coalitions_tested = tracing::field::Empty,
        survivor_checks = tracing::field::Empty,
    )
)]
pub fn check_full_consistency_audit(
    rule: &Rule,
    claims: &[Claim],
    estate: &Estate,
    options: FullConsistencyOptions,
) -> Result<FullConsistencyAudit, LegitimacyError> {
    if matches!(options.mode, ConsistencyMode::Full) {
        validate_full_complexity_gate(claims.len(), options.allow_exponential_consistency)?;
    }

    let audit = check_consistency_with_mode(rule, claims, estate, options.mode)?;
    tracing::Span::current().record(
        "result",
        tracing::field::display(verdict_result(&audit.verdict)),
    );
    tracing::Span::current().record(
        "coalitions_tested",
        tracing::field::display(audit.complexity.coalitions_tested),
    );
    tracing::Span::current().record(
        "survivor_checks",
        tracing::field::display(audit.complexity.survivor_checks),
    );
    Ok(audit)
}

/// Exact rational full-consistency checker for theorem-backed parity fixtures.
/// Operational diagnostics keep using f64 rules; this path avoids tolerance and
/// rounding when binding Rust output to the Lean `YoungFullConsistencyOn`
/// contract.
pub fn check_full_consistency_rational<F>(
    allocate: F,
    claims: &[RationalClaim],
    estate: &RationalEstate,
    options: FullConsistencyOptions,
) -> Result<RationalFullConsistencyAuditArtifact, LegitimacyError>
where
    F: Fn(&[RationalClaim], &RationalEstate) -> Result<RationalAllocation, LegitimacyError>,
{
    if matches!(options.mode, ConsistencyMode::Full) {
        validate_full_complexity_gate(claims.len(), options.allow_exponential_consistency)?;
    }

    let original_allocation = allocate(claims, estate)?;
    let mut complexity = ConsistencyComplexity::default();

    for removed_indices in CoalitionEnumeration::new(claims.len(), options.mode) {
        let removed_ids: Vec<String> = removed_indices
            .iter()
            .map(|index| claims[*index].claimant_id.clone())
            .collect();
        let removed_lookup = removed_lookup(claims.len(), &removed_indices);
        let reduced_claims: Vec<RationalClaim> = claims
            .iter()
            .enumerate()
            .filter(|(index, _)| !removed_lookup[*index])
            .map(|(_, claim)| claim.clone())
            .collect();
        let removed_total = removed_ids.iter().try_fold(
            ConsistencyRational::from_integer(0),
            |acc, claimant_id| {
                rational_share(&original_allocation, claimant_id, "rational removed share")
                    .map(|share| acc + share)
            },
        )?;
        let reduced_total = estate.total - removed_total;
        complexity.coalitions_tested += 1;
        if reduced_claims.is_empty() || reduced_total <= ConsistencyRational::from_integer(0) {
            continue;
        }
        let reduced_estate = RationalEstate::new(reduced_total, estate.unit.clone())?;
        let reduced_allocation = allocate(&reduced_claims, &reduced_estate)?;

        for claim in &reduced_claims {
            complexity.survivor_checks += 1;
            let original_share = rational_share(
                &original_allocation,
                &claim.claimant_id,
                "rational original share",
            )?;
            let reduced_share = rational_share(
                &reduced_allocation,
                &claim.claimant_id,
                "rational reduced share",
            )?;
            if original_share != reduced_share {
                return Ok(RationalFullConsistencyAuditArtifact {
                    verdict: RationalFullConsistencyVerdict::Rejected(
                        RationalConsistencyCounterexample {
                            removed: removed_ids,
                            survivor: claim.claimant_id.clone(),
                            original_share,
                            reduced_share,
                        },
                    ),
                    complexity,
                });
            }
        }
    }

    Ok(RationalFullConsistencyAuditArtifact {
        verdict: RationalFullConsistencyVerdict::Admissible,
        complexity,
    })
}

/// Check public Young consistency by enumerating every non-empty proper removed
/// coalition and verifying that survivor allocations are preserved.
#[tracing::instrument(
    skip(rule, claims, estate),
    fields(axiom_name = "consistency", result = tracing::field::Empty)
)]
pub fn check_consistency(
    rule: &Rule,
    claims: &[Claim],
    estate: &Estate,
) -> Result<Verdict, LegitimacyError> {
    check_full_consistency(rule, claims, estate, FullConsistencyOptions::default())
}

/// Check a bounded, explicitly labeled approximation to Young consistency.
pub fn check_bounded_consistency(
    rule: &Rule,
    claims: &[Claim],
    estate: &Estate,
    max_removed: usize,
) -> Result<Verdict, LegitimacyError> {
    Ok(check_consistency_with_mode(
        rule,
        claims,
        estate,
        ConsistencyMode::Bounded { max_removed },
    )?
    .verdict)
}

/// Historical singles+pairs diagnostic retained for mutation tests and
/// operational comparisons. Public release checks should use
/// `check_consistency` or `check_full_consistency`.
pub fn check_singles_pairs_consistency(
    rule: &Rule,
    claims: &[Claim],
    estate: &Estate,
) -> Result<Verdict, LegitimacyError> {
    check_bounded_consistency(rule, claims, estate, 2)
}

fn check_consistency_with_mode(
    rule: &Rule,
    claims: &[Claim],
    estate: &Estate,
    mode: ConsistencyMode,
) -> Result<FullConsistencyAudit, LegitimacyError> {
    let original_allocation = evaluate_rule(rule, claims, estate, "consistency baseline")?;
    let mut complexity = ConsistencyComplexity::default();
    let axiom = axiom_label(mode);

    // CoalitionEnumeration yields strict index combinations: an index can occur
    // at most once in a removed coalition. On the distinct-claimant profiles
    // covered by Lean `ClaimsDistinct`, this matches
    // `ClaimantIdsProperSubset`'s duplicate-free removed-ID requirement.
    for removed_indices in CoalitionEnumeration::new(claims.len(), mode) {
        if let Some(verdict) = evaluate_reduction(
            rule,
            claims,
            estate,
            &original_allocation,
            &removed_indices,
            &mut complexity,
            &axiom,
        )? {
            return Ok(FullConsistencyAudit {
                verdict,
                complexity,
            });
        }
    }

    let verdict = Verdict::Admissible {
        axiom,
        perturbations_tested: complexity.coalitions_tested,
    };
    Ok(FullConsistencyAudit {
        verdict,
        complexity,
    })
}

fn verdict_result(verdict: &Verdict) -> &'static str {
    match verdict {
        Verdict::Admissible { .. } => "admissible",
        Verdict::Rejected { .. } => "rejected",
    }
}

fn rational_share(
    allocation: &RationalAllocation,
    claimant_id: &str,
    context: &str,
) -> Result<ConsistencyRational, LegitimacyError> {
    allocation
        .get(claimant_id)
        .cloned()
        .ok_or_else(|| LegitimacyError::missing_allocation_share(claimant_id.to_string(), context))
}

fn evaluate_reduction(
    rule: &Rule,
    claims: &[Claim],
    estate: &Estate,
    original_allocation: &ValidAllocation,
    removed_indices: &[usize],
    complexity: &mut ConsistencyComplexity,
    axiom: &str,
) -> Result<Option<Verdict>, LegitimacyError> {
    let removed_ids: Vec<String> = removed_indices
        .iter()
        .map(|index| claims[*index].claimant_id.clone())
        .collect();
    let removed_lookup = removed_lookup(claims.len(), removed_indices);
    let reduced_claims: Vec<Claim> = claims
        .iter()
        .enumerate()
        .filter(|(index, _)| !removed_lookup[*index])
        .map(|(_, claim)| claim.clone())
        .collect();
    let reduced_total: f64 = reduced_claims
        .iter()
        .map(|claim| {
            original_allocation
                .share_for(&claim.claimant_id, "consistency reduction surviving share")
        })
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .sum();
    complexity.coalitions_tested += 1;
    if reduced_claims.is_empty() || reduced_total <= EPSILON {
        return Ok(None);
    }
    let reduced_estate = Estate::new(reduced_total, estate.unit.clone())?;
    let reduced_allocation = evaluate_rule(
        rule,
        &reduced_claims,
        &reduced_estate,
        "consistency reduction",
    )?;

    for claim in &reduced_claims {
        complexity.survivor_checks += 1;
        let original_share =
            original_allocation.share_for(&claim.claimant_id, "consistency original share")?;
        let reduced_share =
            reduced_allocation.share_for(&claim.claimant_id, "consistency reduced share")?;

        if (original_share - reduced_share).abs()
            > EPSILON + EPSILON * (original_share.abs() + reduced_share.abs())
        {
            let affected_id = claim.claimant_id.clone();
            let removed_label = removed_ids.join(", ");
            return Ok(Some(Verdict::Rejected {
                axiom: axiom.to_string(),
                counterexample: Counterexample {
                    description: format!(
                        "Coalition witness [{}] changed '{}' allocation from {:.4} to {:.4}",
                        removed_label, affected_id, original_share, reduced_share
                    ),
                    original_claims: claims.to_vec(),
                    original_estate: estate.clone(),
                    original_allocation: original_allocation.clone(),
                    perturbed_claims: reduced_claims,
                    perturbed_estate: reduced_estate,
                    perturbed_allocation: reduced_allocation,
                    violation: format!(
                        "Removing coalition [{}] changed the allocation of '{}'. \
                         The rule's verdict depends on who is in the room, not just on the \
                         surviving claimants' claims against the reduced estate. \
                         coalitions_tested={}, survivor_checks={}",
                        removed_label,
                        affected_id,
                        complexity.coalitions_tested,
                        complexity.survivor_checks
                    ),
                },
            }));
        }
    }

    Ok(None)
}

fn validate_full_complexity_gate(
    claimant_count: usize,
    allow_exponential_consistency: bool,
) -> Result<(), LegitimacyError> {
    if claimant_count == FULL_CONSISTENCY_WARN_CLAIMANTS {
        tracing::warn!(
            claimant_count,
            "full Young consistency enumerates exponentially many coalitions"
        );
    }

    if claimant_count > FULL_CONSISTENCY_WARN_CLAIMANTS && !allow_exponential_consistency {
        return Err(LegitimacyError::invalid_input(format!(
            "full Young consistency for {claimant_count} claimants requires --allow-exponential-consistency"
        )));
    }

    Ok(())
}

fn axiom_label(mode: ConsistencyMode) -> String {
    match mode {
        ConsistencyMode::Full => "consistency (Young full sub-coalition)".to_string(),
        ConsistencyMode::Bounded { max_removed: 2 } => {
            "consistency (single-claimant and pair reductions)".to_string()
        }
        ConsistencyMode::Bounded { max_removed } => {
            format!("consistency (bounded sub-coalitions, max_removed={max_removed})")
        }
    }
}

fn removed_lookup(claim_count: usize, removed_indices: &[usize]) -> Vec<bool> {
    let mut lookup = vec![false; claim_count];
    for index in removed_indices {
        lookup[*index] = true;
    }
    lookup
}

struct CoalitionEnumeration {
    claim_count: usize,
    next_size: usize,
    max_removed: usize,
    current: Option<CoalitionSizeEnumeration>,
}

impl CoalitionEnumeration {
    fn new(claim_count: usize, mode: ConsistencyMode) -> Self {
        let max_removed = match mode {
            ConsistencyMode::Full => claim_count.saturating_sub(1),
            ConsistencyMode::Bounded { max_removed } => {
                max_removed.min(claim_count.saturating_sub(1))
            }
        };
        Self {
            claim_count,
            next_size: 1,
            max_removed,
            current: None,
        }
    }
}

impl Iterator for CoalitionEnumeration {
    type Item = Vec<usize>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(current) = &mut self.current
                && let Some(indices) = current.next()
            {
                return Some(indices);
            }

            if self.next_size > self.max_removed {
                return None;
            }

            self.current = Some(CoalitionSizeEnumeration::new(
                self.claim_count,
                self.next_size,
            ));
            self.next_size += 1;
        }
    }
}

enum CoalitionSizeEnumeration {
    Bitset(BitsetCoalitions),
    Vector(VecCoalitions),
}

impl CoalitionSizeEnumeration {
    fn new(claim_count: usize, coalition_size: usize) -> Self {
        if claim_count <= 63 {
            Self::Bitset(BitsetCoalitions::new(claim_count, coalition_size))
        } else {
            Self::Vector(VecCoalitions::new(claim_count, coalition_size))
        }
    }
}

impl Iterator for CoalitionSizeEnumeration {
    type Item = Vec<usize>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Bitset(iter) => iter.next(),
            Self::Vector(iter) => iter.next(),
        }
    }
}

struct BitsetCoalitions {
    claim_count: usize,
    next_mask: Option<u64>,
}

impl BitsetCoalitions {
    fn new(claim_count: usize, coalition_size: usize) -> Self {
        let next_mask = if coalition_size == 0 || coalition_size > claim_count {
            None
        } else {
            Some((1_u64 << coalition_size) - 1)
        };
        Self {
            claim_count,
            next_mask,
        }
    }
}

impl Iterator for BitsetCoalitions {
    type Item = Vec<usize>;

    fn next(&mut self) -> Option<Self::Item> {
        let mask = self.next_mask?;
        let limit = 1_u64 << self.claim_count;
        let next = next_same_popcount(mask);
        self.next_mask = next.filter(|next_mask| *next_mask < limit);
        Some(mask_to_indices(mask, self.claim_count))
    }
}

fn next_same_popcount(mask: u64) -> Option<u64> {
    let smallest = mask & mask.wrapping_neg();
    let ripple = mask.checked_add(smallest)?;
    let ones = mask ^ ripple;
    Some(((ones >> 2) / smallest) | ripple)
}

fn mask_to_indices(mask: u64, claim_count: usize) -> Vec<usize> {
    (0..claim_count)
        .filter(|index| (mask & (1_u64 << index)) != 0)
        .collect()
}

struct VecCoalitions {
    claim_count: usize,
    current: Option<Vec<usize>>,
}

impl VecCoalitions {
    fn new(claim_count: usize, coalition_size: usize) -> Self {
        let current = if coalition_size == 0 || coalition_size > claim_count {
            None
        } else {
            Some((0..coalition_size).collect())
        };
        Self {
            claim_count,
            current,
        }
    }
}

impl Iterator for VecCoalitions {
    type Item = Vec<usize>;

    fn next(&mut self) -> Option<Self::Item> {
        let result = self.current.clone()?;
        self.current = next_vec_combination(&result, self.claim_count);
        Some(result)
    }
}

fn next_vec_combination(current: &[usize], claim_count: usize) -> Option<Vec<usize>> {
    let coalition_size = current.len();
    let mut next = current.to_vec();
    for position in (0..coalition_size).rev() {
        let max_at_position = claim_count - coalition_size + position;
        if next[position] < max_at_position {
            next[position] += 1;
            for suffix in position + 1..coalition_size {
                next[suffix] = next[suffix - 1] + 1;
            }
            return Some(next);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::CoalitionEnumeration;
    use crate::{
        Claim, Estate, Rule, RuleSpec, Verdict,
        axioms::consistency::{
            ConsistencyMode, FullConsistencyOptions, check_consistency, check_full_consistency,
            check_full_consistency_audit,
        },
        rules::proportional_rule,
    };

    #[test]
    fn proportional_rule_is_consistent() {
        let claims = vec![
            Claim::new("alice", 1.0).unwrap(),
            Claim::new("bob", 2.0).unwrap(),
            Claim::new("carol", 3.0).unwrap(),
        ];
        let estate = Estate::new(6.0, "units").unwrap();

        let verdict = check_consistency(&proportional_rule(), &claims, &estate);
        assert!(matches!(verdict, Ok(Verdict::Admissible { .. })));
    }

    #[test]
    fn proportional_rule_consistent_large_estate() {
        // Regression: absolute EPSILON=1e-9 triggered false Rejected for estates >1e7
        // due to float-cancellation in reduced_total = estate - removed_share.
        // Fix uses relative tolerance so this passes at estate=1e12.
        let claims = vec![
            Claim::new("alice", 90.9).unwrap(),
            Claim::new("bob", 14.6).unwrap(),
        ];
        let estate = Estate::new(1e12, "units").unwrap();
        let verdict = check_consistency(&proportional_rule(), &claims, &estate);
        assert!(
            matches!(verdict, Ok(Verdict::Admissible { .. })),
            "proportional rule must be consistent at large estate; got: {verdict:?}"
        );
    }

    #[test]
    fn pair_sensitive_rule_is_rejected() {
        let rule = Rule {
            name: "pair-sensitive".to_string(),
            version: "0.1.0".to_string(),
            rule_spec: RuleSpec::programmatic(|claims: &[Claim], estate: &Estate| {
                let mut allocation = crate::Allocation::default();
                if claims.len() == 2 {
                    let bonus = estate.total.value() / 2.0;
                    allocation.insert(claims[0].claimant_id.clone(), bonus);
                    allocation.insert(claims[1].claimant_id.clone(), 0.0);
                } else {
                    let total_strength: f64 =
                        claims.iter().map(|claim| claim.strength.value()).sum();
                    for claim in claims {
                        allocation.insert(
                            claim.claimant_id.clone(),
                            estate.total.value() * claim.strength.value() / total_strength,
                        );
                    }
                }
                Ok(allocation)
            }),
            priority_classes: vec!["standard".to_string()],
        };
        let claims = vec![
            Claim::new("alice", 1.0).unwrap(),
            Claim::new("bob", 2.0).unwrap(),
            Claim::new("carol", 3.0).unwrap(),
            Claim::new("dave", 4.0).unwrap(),
        ];
        let estate = Estate::new(10.0, "units").unwrap();

        let verdict = check_consistency(&rule, &claims, &estate);

        assert!(
            matches!(verdict, Ok(Verdict::Rejected { .. })),
            "pair-sensitive rule must fail pair-reduction consistency; got: {verdict:?}"
        );
        if let Ok(Verdict::Rejected { counterexample, .. }) = verdict {
            assert!(
                counterexample
                    .description
                    .contains("Coalition witness [alice, bob]")
                    || counterexample
                        .description
                        .contains("Coalition witness [alice, carol]")
                    || counterexample
                        .description
                        .contains("Coalition witness [alice, dave]")
                    || counterexample
                        .description
                        .contains("Coalition witness [bob, carol]")
                    || counterexample
                        .description
                        .contains("Coalition witness [bob, dave]")
                    || counterexample
                        .description
                        .contains("Coalition witness [carol, dave]")
            );
        }
    }

    #[test]
    fn full_consistency_counts_every_proper_nonempty_subcoalition() {
        let claims = vec![
            Claim::new("alice", 1.0).unwrap(),
            Claim::new("bob", 2.0).unwrap(),
            Claim::new("carol", 3.0).unwrap(),
            Claim::new("dave", 4.0).unwrap(),
        ];
        let estate = Estate::new(10.0, "units").unwrap();

        let audit = check_full_consistency_audit(
            &proportional_rule(),
            &claims,
            &estate,
            FullConsistencyOptions::default(),
        )
        .unwrap();

        assert!(matches!(
            audit.verdict,
            Verdict::Admissible {
                ref axiom,
                perturbations_tested: 14,
            } if axiom == "consistency (Young full sub-coalition)"
        ));
        assert_eq!(audit.complexity.coalitions_tested, 14);
        assert_eq!(audit.complexity.survivor_checks, 28);
    }

    #[test]
    fn bounded_consistency_counts_only_requested_cardinalities() {
        let claims = vec![
            Claim::new("alice", 1.0).unwrap(),
            Claim::new("bob", 2.0).unwrap(),
            Claim::new("carol", 3.0).unwrap(),
            Claim::new("dave", 4.0).unwrap(),
        ];
        let estate = Estate::new(10.0, "units").unwrap();

        let audit = check_full_consistency_audit(
            &proportional_rule(),
            &claims,
            &estate,
            FullConsistencyOptions {
                mode: ConsistencyMode::Bounded { max_removed: 1 },
                allow_exponential_consistency: false,
            },
        )
        .unwrap();

        assert_eq!(audit.complexity.coalitions_tested, 4);
        assert_eq!(audit.complexity.survivor_checks, 12);
        assert!(matches!(
            audit.verdict,
            Verdict::Admissible {
                ref axiom,
                perturbations_tested: 4,
            } if axiom == "consistency (bounded sub-coalitions, max_removed=1)"
        ));
    }

    #[test]
    fn full_consistency_requires_explicit_exponential_opt_in_above_gate() {
        let claims = (0..21)
            .map(|index| Claim::new(format!("claimant-{index}"), index as f64 + 1.0).unwrap())
            .collect::<Vec<_>>();
        let estate = Estate::new(231.0, "units").unwrap();

        let error =
            check_full_consistency(&proportional_rule(), &claims, &estate, Default::default())
                .unwrap_err();

        assert!(
            error
                .to_string()
                .contains("--allow-exponential-consistency"),
            "{error}"
        );
    }

    #[test]
    fn coalition_enumeration_is_cardinality_then_lexicographic() {
        let coalitions = CoalitionEnumeration::new(4, ConsistencyMode::Full).collect::<Vec<_>>();
        assert_eq!(
            coalitions,
            vec![
                vec![0],
                vec![1],
                vec![2],
                vec![3],
                vec![0, 1],
                vec![0, 2],
                vec![1, 2],
                vec![0, 3],
                vec![1, 3],
                vec![2, 3],
                vec![0, 1, 2],
                vec![0, 1, 3],
                vec![0, 2, 3],
                vec![1, 2, 3],
            ]
        );
    }

    #[test]
    fn large_claim_sets_use_vector_combination_order() {
        let coalitions = CoalitionEnumeration::new(64, ConsistencyMode::Bounded { max_removed: 1 })
            .take(4)
            .collect::<Vec<_>>();
        assert_eq!(coalitions, vec![vec![0], vec![1], vec![2], vec![3]]);
    }
}
