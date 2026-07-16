use crate::{Allocation, Claim, EPSILON, Estate, LegitimacyError, Rule, RuleSpec, validate_claims};

/// Jefferson / d'Hondt in highest-averages form.
///
/// This is equivalent to the floor-divisor family, but the seat-by-seat form
/// gives deterministic tie-breaking and exact whole-seat allocation for integer
/// estates.
#[tracing::instrument]
pub fn jefferson_rule() -> Rule {
    Rule {
        name: "jefferson".to_string(),
        version: "1.0.0".to_string(),
        rule_spec: RuleSpec::programmatic(jefferson_allocate),
        priority_classes: vec!["standard".to_string()],
    }
}

/// Webster / Sainte-Lague in highest-averages form.
///
/// This is equivalent to the round-to-nearest divisor family, but the
/// highest-averages implementation keeps the whole-seat apportionment exact.
#[tracing::instrument]
pub fn webster_rule() -> Rule {
    Rule {
        name: "webster".to_string(),
        version: "1.0.0".to_string(),
        rule_spec: RuleSpec::programmatic(webster_allocate),
        priority_classes: vec!["standard".to_string()],
    }
}

/// Jefferson / d'Hondt allocation.
///
/// Interprets the estate as a whole-seat house size and awards `floor(estate)`
/// seats using the divisor sequence `1, 2, 3, ...`.
pub fn jefferson_allocate(
    claims: &[Claim],
    estate: &Estate,
) -> Result<Allocation, LegitimacyError> {
    highest_averages_allocate(claims, estate, DivisorFamily::Jefferson)
}

/// Webster / Sainte-Lague allocation.
///
/// Interprets the estate as a whole-seat house size and awards `floor(estate)`
/// seats using the divisor sequence `1, 3, 5, ...`.
pub fn webster_allocate(claims: &[Claim], estate: &Estate) -> Result<Allocation, LegitimacyError> {
    highest_averages_allocate(claims, estate, DivisorFamily::Webster)
}

#[derive(Clone, Copy)]
enum DivisorFamily {
    Jefferson,
    Webster,
}

fn highest_averages_allocate(
    claims: &[Claim],
    estate: &Estate,
    family: DivisorFamily,
) -> Result<Allocation, LegitimacyError> {
    let context = match family {
        DivisorFamily::Jefferson => "jefferson rule",
        DivisorFamily::Webster => "webster rule",
    };
    validate_claims(claims, context)?;

    let seats = estate.total.value().floor() as usize;
    let mut awarded = vec![0usize; claims.len()];

    for _ in 0..seats {
        let mut best_index = None;
        let mut best_quotient = f64::NEG_INFINITY;

        for (index, claim) in claims.iter().enumerate() {
            let quotient = quotient(claim.strength.value(), awarded[index], family);
            if quotient > best_quotient + EPSILON {
                best_index = Some(index);
                best_quotient = quotient;
            }
        }

        if let Some(best_index) = best_index {
            awarded[best_index] += 1;
        }
    }

    Ok(claims
        .iter()
        .enumerate()
        .map(|(index, claim)| (claim.claimant_id.clone(), awarded[index] as f64))
        .collect())
}

fn quotient(strength: f64, awarded: usize, family: DivisorFamily) -> f64 {
    match family {
        DivisorFamily::Jefferson => strength / (awarded + 1) as f64,
        DivisorFamily::Webster => strength / (2 * awarded + 1) as f64,
    }
}

#[cfg(test)]
mod tests {
    use crate::{Claim, Estate};

    use super::{jefferson_allocate, webster_allocate};

    #[test]
    fn jefferson_spends_the_integer_house_size() {
        let claims = vec![
            Claim::new("alpha", 60.0).unwrap(),
            Claim::new("bravo", 30.0).unwrap(),
            Claim::new("charlie", 10.0).unwrap(),
        ];
        let estate = Estate::new(5.0, "seats").unwrap();

        let allocation = jefferson_allocate(&claims, &estate).unwrap();

        assert_eq!(
            allocation.share_for("alpha", "jefferson test").unwrap(),
            4.0
        );
        assert_eq!(
            allocation.share_for("bravo", "jefferson test").unwrap(),
            1.0
        );
        assert_eq!(
            allocation.share_for("charlie", "jefferson test").unwrap(),
            0.0
        );
    }

    #[test]
    fn webster_spends_the_integer_house_size() {
        let claims = vec![
            Claim::new("alpha", 60.0).unwrap(),
            Claim::new("bravo", 30.0).unwrap(),
            Claim::new("charlie", 10.0).unwrap(),
        ];
        let estate = Estate::new(5.0, "seats").unwrap();

        let allocation = webster_allocate(&claims, &estate).unwrap();

        assert_eq!(allocation.share_for("alpha", "webster test").unwrap(), 3.0);
        assert_eq!(allocation.share_for("bravo", "webster test").unwrap(), 2.0);
        assert_eq!(
            allocation.share_for("charlie", "webster test").unwrap(),
            0.0
        );
    }
}
