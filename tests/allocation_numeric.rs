use legitimacy::{Allocation, Claim, Estate};

#[test]
fn feasibility_rejects_overflowing_totals_and_preserves_finite_boundaries() {
    let estate = Estate {
        total: f64::MAX.try_into().unwrap(),
        unit: "test".into(),
    };
    let claims = vec![Claim::new("a", 1.0).unwrap(), Claim::new("b", 1.0).unwrap()];
    for (left, right, feasible) in [
        (f64::MAX, f64::MAX, false),
        (f64::MAX * 0.75, f64::MAX * 0.75, false),
        (f64::MAX * 0.60, f64::MAX * 0.30, true),
        (f64::MAX / 2.0, f64::MAX / 2.0, true),
    ] {
        let allocation: Allocation = [("a".to_string(), left), ("b".to_string(), right)]
            .into_iter()
            .collect();
        let valid = allocation.try_into_valid(&claims).unwrap();
        assert_eq!(
            valid.validate_feasible(&estate).is_ok(),
            feasible,
            "{left} + {right}"
        );
    }
    let estate = Estate {
        total: (f64::MAX / 2.0).try_into().unwrap(),
        unit: "test".into(),
    };
    let oversized: Allocation = [("a".to_string(), f64::MAX * 0.8)].into_iter().collect();
    assert!(oversized.validate_feasible(&estate).is_err());
}
