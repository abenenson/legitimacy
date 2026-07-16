use legitimacy::{
    ConsistencyComplexity, ConsistencyRational, FullConsistencyOptions, RationalAllocation,
    RationalClaim, RationalEstate, RationalFullConsistencyVerdict, check_full_consistency_rational,
};
use serde::Serialize;
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
};

const FIXTURE_PATH: &str = "tests/fixtures/young_full_consistency_rational.json";

#[derive(Serialize)]
struct ParityFixture {
    schema_version: &'static str,
    lean_theorem: &'static str,
    mode: &'static str,
    claims: Vec<ClaimFixture>,
    estate: EstateFixture,
    original_allocation: Vec<AllocationFixture>,
    reductions: Vec<ReductionFixture>,
    audit: AuditFixture,
}

#[derive(Serialize)]
struct ClaimFixture {
    claimant_id: String,
    strength: String,
}

#[derive(Serialize)]
struct EstateFixture {
    total: String,
    unit: String,
}

#[derive(Serialize)]
struct AllocationFixture {
    claimant_id: String,
    share: String,
}

#[derive(Serialize)]
struct ReductionFixture {
    removed: Vec<String>,
    reduced_estate: String,
    allocation: Vec<AllocationFixture>,
}

#[derive(Serialize)]
struct AuditFixture {
    verdict: &'static str,
    coalitions_tested: usize,
    survivor_checks: usize,
}

#[test]
fn young_full_consistency_rational_fixture_is_byte_stable() {
    let fixture = build_fixture();
    let mut actual = serde_json::to_vec_pretty(&fixture).unwrap();
    actual.push(b'\n');
    let expected = fs::read(Path::new(FIXTURE_PATH)).unwrap();
    assert_eq!(
        actual, expected,
        "rational Young consistency parity fixture drifted"
    );
}

#[test]
fn duplicate_removed_ids_are_not_canonical_young_coalitions() {
    let claims = rational_claims();
    let estate = RationalEstate::new(rational(6, 1), "units").unwrap();
    let original_allocation = proportional_rational(&claims, &estate).unwrap();

    let duplicate_removed = ["alice", "alice"];
    let duplicate_removed_total = duplicate_removed
        .iter()
        .fold(rational(0, 1), |acc, claimant_id| {
            acc + *original_allocation.get(*claimant_id).unwrap()
        });
    let single_removed_total = *original_allocation.get("alice").unwrap();

    assert_eq!(single_removed_total, rational(1, 1));
    assert_eq!(duplicate_removed_total, rational(2, 1));

    let audit = check_full_consistency_rational(
        proportional_rational,
        &claims,
        &estate,
        FullConsistencyOptions::default(),
    )
    .unwrap();
    assert_eq!(audit.verdict, RationalFullConsistencyVerdict::Admissible);
    assert_eq!(
        audit.complexity,
        ConsistencyComplexity {
            coalitions_tested: 6,
            survivor_checks: 9,
        }
    );

    for reduction in reductions_fixture(&claims, &estate, &original_allocation) {
        let unique_removed = reduction.removed.iter().collect::<BTreeSet<_>>();
        assert_eq!(
            unique_removed.len(),
            reduction.removed.len(),
            "canonical Young removed coalition must be duplicate-free: {:?}",
            reduction.removed
        );
    }
}

fn build_fixture() -> ParityFixture {
    let claims = rational_claims();
    let estate = RationalEstate::new(rational(6, 1), "units").unwrap();
    let original_allocation = proportional_rational(&claims, &estate).unwrap();
    let audit = check_full_consistency_rational(
        proportional_rational,
        &claims,
        &estate,
        FullConsistencyOptions::default(),
    )
    .unwrap();
    assert_eq!(audit.verdict, RationalFullConsistencyVerdict::Admissible);
    assert_eq!(
        audit.complexity,
        ConsistencyComplexity {
            coalitions_tested: 6,
            survivor_checks: 9,
        }
    );

    ParityFixture {
        schema_version: "young-full-consistency-rational-v1",
        lean_theorem: "lean_full_consistency_executable_iff_axiom",
        mode: "full",
        claims: claims
            .iter()
            .map(|claim| ClaimFixture {
                claimant_id: claim.claimant_id.clone(),
                strength: format_rational(&claim.strength),
            })
            .collect(),
        estate: EstateFixture {
            total: format_rational(&estate.total),
            unit: estate.unit.clone(),
        },
        original_allocation: allocation_fixture(&original_allocation),
        reductions: reductions_fixture(&claims, &estate, &original_allocation),
        audit: AuditFixture {
            verdict: "admissible",
            coalitions_tested: audit.complexity.coalitions_tested,
            survivor_checks: audit.complexity.survivor_checks,
        },
    }
}

fn rational_claims() -> Vec<RationalClaim> {
    vec![
        RationalClaim::new("alice", rational(1, 1)).unwrap(),
        RationalClaim::new("bob", rational(2, 1)).unwrap(),
        RationalClaim::new("carol", rational(3, 1)).unwrap(),
    ]
}

fn proportional_rational(
    claims: &[RationalClaim],
    estate: &RationalEstate,
) -> Result<RationalAllocation, legitimacy::LegitimacyError> {
    let total_strength = claims
        .iter()
        .fold(rational(0, 1), |acc, claim| acc + claim.strength);
    let mut allocation = RationalAllocation::new();
    for claim in claims {
        allocation.insert(
            claim.claimant_id.clone(),
            estate.total * claim.strength / total_strength,
        );
    }
    Ok(allocation)
}

fn reductions_fixture(
    claims: &[RationalClaim],
    estate: &RationalEstate,
    original_allocation: &RationalAllocation,
) -> Vec<ReductionFixture> {
    let coalitions = [
        vec![0],
        vec![1],
        vec![2],
        vec![0, 1],
        vec![0, 2],
        vec![1, 2],
    ];
    coalitions
        .into_iter()
        .map(|removed_indices| {
            let removed = removed_indices
                .iter()
                .map(|index| claims[*index].claimant_id.clone())
                .collect::<Vec<_>>();
            let removed_total = removed.iter().fold(rational(0, 1), |acc, claimant_id| {
                acc + *original_allocation.get(claimant_id).unwrap()
            });
            let reduced_claims = claims
                .iter()
                .enumerate()
                .filter(|(index, _)| !removed_indices.contains(index))
                .map(|(_, claim)| claim.clone())
                .collect::<Vec<_>>();
            let reduced_estate =
                RationalEstate::new(estate.total - removed_total, estate.unit.clone()).unwrap();
            let allocation = proportional_rational(&reduced_claims, &reduced_estate).unwrap();
            ReductionFixture {
                removed,
                reduced_estate: format_rational(&reduced_estate.total),
                allocation: allocation_fixture(&allocation),
            }
        })
        .collect()
}

fn allocation_fixture(
    allocation: &BTreeMap<String, ConsistencyRational>,
) -> Vec<AllocationFixture> {
    allocation
        .iter()
        .map(|(claimant_id, share)| AllocationFixture {
            claimant_id: claimant_id.clone(),
            share: format_rational(share),
        })
        .collect()
}

fn rational(numerator: i64, denominator: i64) -> ConsistencyRational {
    ConsistencyRational::new(numerator, denominator)
}

fn format_rational(value: &ConsistencyRational) -> String {
    if *value.denom() == 1 {
        value.numer().to_string()
    } else {
        format!("{}/{}", value.numer(), value.denom())
    }
}
