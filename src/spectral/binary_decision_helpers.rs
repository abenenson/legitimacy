use legitimacy::spectral::positive_procedure::BinaryDecision;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum BinaryDecisionEntropyError {
    NegativeMass { permit: f64, deny: f64 },
    NonFiniteMass { permit: f64, deny: f64 },
    TotalMassNotOne { permit: f64, deny: f64 },
}

pub fn binary_decision_equiv_bool(decision: BinaryDecision) -> bool {
    match decision {
        BinaryDecision::Permit => true,
        BinaryDecision::Deny => false,
    }
}

pub fn bool_equiv_binary_decision(value: bool) -> BinaryDecision {
    if value {
        BinaryDecision::Permit
    } else {
        BinaryDecision::Deny
    }
}

pub fn sum_binary_decision<F>(f: F) -> f64
where
    F: Fn(BinaryDecision) -> f64,
{
    f(BinaryDecision::Permit) + f(BinaryDecision::Deny)
}

pub fn binary_decision_entropy(permit: f64, deny: f64) -> Result<f64, BinaryDecisionEntropyError> {
    validate_binary_probability(permit, deny)?;
    Ok(neg_mul_log(permit) + neg_mul_log(deny))
}

pub fn binary_decision_entropy_le_log_two(
    permit: f64,
    deny: f64,
) -> Result<bool, BinaryDecisionEntropyError> {
    Ok(binary_decision_entropy(permit, deny)? <= std::f64::consts::LN_2 + 1e-12)
}

fn validate_binary_probability(permit: f64, deny: f64) -> Result<(), BinaryDecisionEntropyError> {
    if !permit.is_finite() || !deny.is_finite() {
        return Err(BinaryDecisionEntropyError::NonFiniteMass { permit, deny });
    }
    if permit < 0.0 || deny < 0.0 {
        return Err(BinaryDecisionEntropyError::NegativeMass { permit, deny });
    }
    if (permit + deny - 1.0).abs() > 1e-12 {
        return Err(BinaryDecisionEntropyError::TotalMassNotOne { permit, deny });
    }
    Ok(())
}

fn neg_mul_log(value: f64) -> f64 {
    if value == 0.0 {
        0.0
    } else {
        -value * value.ln()
    }
}

#[cfg(test)]
mod tests {
    use super::{
        binary_decision_entropy, binary_decision_entropy_le_log_two, binary_decision_equiv_bool,
        bool_equiv_binary_decision, sum_binary_decision,
    };
    use legitimacy::spectral::positive_procedure::BinaryDecision;

    #[test]
    fn binary_decision_bool_equivalence_round_trips() {
        for decision in [BinaryDecision::Permit, BinaryDecision::Deny] {
            assert_eq!(
                bool_equiv_binary_decision(binary_decision_equiv_bool(decision)),
                decision
            );
        }
    }

    #[test]
    fn sum_binary_decision_matches_two_cases() {
        let sum = sum_binary_decision(|decision| match decision {
            BinaryDecision::Permit => 0.25,
            BinaryDecision::Deny => 0.75,
        });

        assert!((sum - 1.0).abs() < 1e-12);
    }

    #[test]
    fn binary_decision_entropy_is_bounded_by_log_two() {
        assert!(binary_decision_entropy_le_log_two(0.5, 0.5).unwrap());
        assert!(
            (binary_decision_entropy(0.5, 0.5).unwrap() - std::f64::consts::LN_2).abs() < 1e-12
        );
        assert!(binary_decision_entropy_le_log_two(1.0, 0.0).unwrap());
    }
}
