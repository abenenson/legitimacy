use legitimacy::{
    GovernanceClaim, GovernanceGraph, LegitimacyError, Verdict,
    axioms::{
        binary::BinaryDelta,
        graph::{consistency::check_graph_consistency, monotonicity::check_graph_monotonicity},
    },
};

const EPSILON: f64 = 1e-9;
const LOWER_SCALE_PROBES: u32 = 16;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BinaryDecision {
    Permit,
    Deny,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PreservedDiagnostic {
    Consistency,
    Monotonicity,
}

pub trait ChannelCapacity {
    fn channel_capacity(&self) -> f64;
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct ExactCapacityCalibration {
    pub capacity: f64,
}

impl ChannelCapacity for ExactCapacityCalibration {
    fn channel_capacity(&self) -> f64 {
        self.capacity
    }
}

pub trait CapacityGraph {
    fn cv(&self, signal: &[f64]) -> f64;

    fn c_star(&self, signal: &[f64], delta: f64) -> f64 {
        delta / self.cv(signal)
    }

    fn capability_response(&self, signal: &[f64], delta: f64, c: f64) -> BinaryDecision {
        if c + EPSILON < self.c_star(signal, delta) {
            BinaryDecision::Deny
        } else {
            BinaryDecision::Permit
        }
    }

    fn sp_violation(&self, signal: &[f64], gamma: f64) -> bool {
        gamma <= self.cv(signal) + EPSILON
    }
}

fn check_lower_scales<F>(scale: f64, mut check: F) -> bool
where
    F: FnMut(f64) -> bool,
{
    (1..=LOWER_SCALE_PROBES).all(|step| {
        let lower_scale = scale * f64::from(step) / f64::from(LOWER_SCALE_PROBES);
        lower_scale > 0.0 && check(lower_scale)
    })
}

#[derive(Clone, Debug, PartialEq)]
pub struct CapacityKernel<G, S = Vec<f64>, C = ExactCapacityCalibration> {
    pub graph: G,
    pub signal: S,
    pub delta: f64,
    pub channel: C,
}

impl<G, S, C> CapacityKernel<G, S, C>
where
    G: CapacityGraph,
    S: AsRef<[f64]>,
    C: ChannelCapacity,
{
    pub fn c_star(&self) -> f64 {
        self.graph.c_star(self.signal.as_ref(), self.delta)
    }

    pub fn cv(&self) -> f64 {
        self.graph.cv(self.signal.as_ref())
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct WellConditionedForCapacity {
    pub tolerance_pos: bool,
    pub cv_pos: bool,
    pub exact_capacity_matches_cv: bool,
    pub tolerance: f64,
    pub cv: f64,
    pub channel_capacity: f64,
}

impl WellConditionedForCapacity {
    pub fn check<G, S, C>(kernel: &CapacityKernel<G, S, C>) -> Result<Self, PositiveProcedureError>
    where
        G: CapacityGraph,
        S: AsRef<[f64]>,
        C: ChannelCapacity,
    {
        let tolerance = kernel.delta;
        let cv = kernel.cv();
        let channel_capacity = kernel.channel.channel_capacity();
        let condition = Self {
            tolerance_pos: tolerance.is_finite() && tolerance > 0.0,
            cv_pos: cv.is_finite() && cv > 0.0,
            exact_capacity_matches_cv: channel_capacity.is_finite()
                && (channel_capacity - cv).abs() <= EPSILON,
            tolerance,
            cv,
            channel_capacity,
        };

        if condition.tolerance_pos && condition.cv_pos && condition.exact_capacity_matches_cv {
            Ok(condition)
        } else {
            Err(PositiveProcedureError::NotWellConditioned(condition))
        }
    }

    pub fn capacity_threshold(&self) -> f64 {
        self.tolerance / self.channel_capacity
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum PositiveProcedureCertificate {
    Consistency {
        capacity_pos: bool,
        c: f64,
        c_star: f64,
        verdict: BinaryDecision,
        no_violation: bool,
        sampled_lower_scales_deny: bool,
        sampled_lower_scales_no_violation: bool,
        capacity_threshold: f64,
    },
    Monotonicity {
        c: f64,
        c_star: f64,
        verdict: BinaryDecision,
        upper_scales_permit: bool,
        capacity_threshold: f64,
    },
}

impl PositiveProcedureCertificate {
    pub fn kind(&self) -> PreservedDiagnostic {
        match self {
            Self::Consistency { .. } => PreservedDiagnostic::Consistency,
            Self::Monotonicity { .. } => PreservedDiagnostic::Monotonicity,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum PositiveProcedureError {
    NonPositiveScale(f64),
    AboveThreshold {
        c: f64,
        c_star: f64,
    },
    NotWellConditioned(WellConditionedForCapacity),
    WrongDiagnostic {
        expected: PreservedDiagnostic,
        actual: PreservedDiagnostic,
    },
}

pub fn governance_certificate<G, S, C>(
    kernel: &CapacityKernel<G, S, C>,
    scale: f64,
) -> Result<PositiveProcedureCertificate, PositiveProcedureError>
where
    G: CapacityGraph,
    S: AsRef<[f64]>,
    C: ChannelCapacity,
{
    if !(scale.is_finite() && scale > 0.0) {
        return Err(PositiveProcedureError::NonPositiveScale(scale));
    }

    let well_conditioned = WellConditionedForCapacity::check(kernel)?;
    let c_star = kernel.c_star();
    if scale > c_star + EPSILON {
        return Err(PositiveProcedureError::AboveThreshold { c: scale, c_star });
    }

    let signal = kernel.signal.as_ref();
    let capacity_threshold = well_conditioned.capacity_threshold();
    if scale + EPSILON < c_star {
        let verdict = kernel
            .graph
            .capability_response(signal, kernel.delta, scale);
        let no_violation = !kernel.graph.sp_violation(signal, kernel.delta / scale);
        let sampled_lower_scales_deny = check_lower_scales(scale, |lower_scale| {
            kernel
                .graph
                .capability_response(signal, kernel.delta, lower_scale)
                == BinaryDecision::Deny
        });
        let sampled_lower_scales_no_violation = check_lower_scales(scale, |lower_scale| {
            !kernel
                .graph
                .sp_violation(signal, kernel.delta / lower_scale)
        });
        Ok(PositiveProcedureCertificate::Consistency {
            capacity_pos: true,
            c: scale,
            c_star,
            verdict,
            no_violation,
            sampled_lower_scales_deny,
            sampled_lower_scales_no_violation,
            capacity_threshold,
        })
    } else {
        Ok(PositiveProcedureCertificate::Monotonicity {
            c: scale,
            c_star,
            verdict: kernel
                .graph
                .capability_response(signal, kernel.delta, scale),
            upper_scales_permit: true,
            capacity_threshold,
        })
    }
}

pub fn governance_certificate_constructible<G, S, C>(
    kernel: &CapacityKernel<G, S, C>,
    scale: f64,
) -> Result<PositiveProcedureCertificate, PositiveProcedureError>
where
    G: CapacityGraph,
    S: AsRef<[f64]>,
    C: ChannelCapacity,
{
    let cert = governance_certificate(kernel, scale)?;
    match cert.kind() {
        PreservedDiagnostic::Consistency | PreservedDiagnostic::Monotonicity => Ok(cert),
    }
}

pub trait GraphDiagnosticCarrier {
    fn graph(&self) -> &GovernanceGraph;
    fn claims(&self) -> &[GovernanceClaim];
    fn monotonicity_deltas(&self) -> &[BinaryDelta];
    fn nontrivial(&self) -> bool;

    fn consistency_from_exact_subcritical(
        &self,
        _certificate: &PositiveProcedureCertificate,
    ) -> Result<Verdict, LegitimacyError> {
        check_graph_consistency(self.graph(), self.claims())
    }

    fn monotonicity_from_boundary(
        &self,
        _certificate: &PositiveProcedureCertificate,
    ) -> Result<Verdict, LegitimacyError> {
        check_graph_monotonicity(self.graph(), self.claims(), self.monotonicity_deltas())
    }
}

pub fn kind_consistency_to_graph_consistency<C>(
    carrier: &C,
    certificate: &PositiveProcedureCertificate,
) -> Result<Verdict, PositiveProcedureError>
where
    C: GraphDiagnosticCarrier,
{
    if certificate.kind() != PreservedDiagnostic::Consistency {
        return Err(PositiveProcedureError::WrongDiagnostic {
            expected: PreservedDiagnostic::Consistency,
            actual: certificate.kind(),
        });
    }

    carrier
        .consistency_from_exact_subcritical(certificate)
        .map_err(|_| PositiveProcedureError::WrongDiagnostic {
            expected: PreservedDiagnostic::Consistency,
            actual: certificate.kind(),
        })
}

pub fn kind_monotonicity_to_graph_monotonicity<C>(
    carrier: &C,
    certificate: &PositiveProcedureCertificate,
) -> Result<Verdict, PositiveProcedureError>
where
    C: GraphDiagnosticCarrier,
{
    if certificate.kind() != PreservedDiagnostic::Monotonicity {
        return Err(PositiveProcedureError::WrongDiagnostic {
            expected: PreservedDiagnostic::Monotonicity,
            actual: certificate.kind(),
        });
    }

    carrier
        .monotonicity_from_boundary(certificate)
        .map_err(|_| PositiveProcedureError::WrongDiagnostic {
            expected: PreservedDiagnostic::Monotonicity,
            actual: certificate.kind(),
        })
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct FixedCvGraph {
    pub cv: f64,
}

impl CapacityGraph for FixedCvGraph {
    fn cv(&self, _signal: &[f64]) -> f64 {
        self.cv
    }
}

pub fn concrete_half_noisy_kernel() -> CapacityKernel<FixedCvGraph> {
    CapacityKernel {
        graph: FixedCvGraph { cv: 0.5 },
        signal: vec![0.0, 0.5, 1.0],
        delta: 0.1,
        channel: ExactCapacityCalibration { capacity: 0.5 },
    }
}

#[cfg(test)]
mod tests {
    use super::{
        BinaryDecision, CapacityGraph, ExactCapacityCalibration, PositiveProcedureCertificate,
        PreservedDiagnostic, concrete_half_noisy_kernel, governance_certificate,
        governance_certificate_constructible,
    };

    #[test]
    fn concrete_half_noisy_certificate_at_one_tenth_is_consistency() {
        let kernel = concrete_half_noisy_kernel();
        let certificate = governance_certificate(&kernel, 0.1).unwrap();

        assert_eq!(certificate.kind(), PreservedDiagnostic::Consistency);
        match certificate {
            PositiveProcedureCertificate::Consistency {
                c_star,
                verdict,
                no_violation,
                sampled_lower_scales_deny,
                sampled_lower_scales_no_violation,
                capacity_threshold,
                ..
            } => {
                assert!((c_star - 0.2).abs() < 1e-9);
                assert_eq!(verdict, BinaryDecision::Deny);
                assert!(no_violation);
                assert!(sampled_lower_scales_deny);
                assert!(sampled_lower_scales_no_violation);
                assert!((capacity_threshold - 0.2).abs() < 1e-9);
            }
            PositiveProcedureCertificate::Monotonicity { .. } => {
                panic!("strict subcritical scale should select consistency")
            }
        }
    }

    #[test]
    fn concrete_half_noisy_certificate_at_boundary_is_monotonicity() {
        let kernel = concrete_half_noisy_kernel();
        let certificate = governance_certificate_constructible(&kernel, 0.2).unwrap();

        assert_eq!(certificate.kind(), PreservedDiagnostic::Monotonicity);
    }

    #[derive(Clone, Copy, Debug, PartialEq)]
    struct LowerScaleMismatchGraph;

    impl CapacityGraph for LowerScaleMismatchGraph {
        fn cv(&self, _signal: &[f64]) -> f64 {
            0.5
        }

        fn capability_response(&self, _signal: &[f64], _delta: f64, c: f64) -> BinaryDecision {
            if (c - 0.1).abs() < 1e-9 {
                BinaryDecision::Deny
            } else {
                BinaryDecision::Permit
            }
        }
    }

    #[test]
    fn consistency_certificate_checks_lower_scale_verdicts_independently() {
        let kernel = super::CapacityKernel {
            graph: LowerScaleMismatchGraph,
            signal: vec![0.0, 0.5, 1.0],
            delta: 0.1,
            channel: ExactCapacityCalibration { capacity: 0.5 },
        };
        let certificate = governance_certificate(&kernel, 0.1).unwrap();

        match certificate {
            PositiveProcedureCertificate::Consistency {
                verdict,
                sampled_lower_scales_deny,
                sampled_lower_scales_no_violation,
                ..
            } => {
                assert_eq!(verdict, BinaryDecision::Deny);
                assert!(!sampled_lower_scales_deny);
                assert!(sampled_lower_scales_no_violation);
            }
            PositiveProcedureCertificate::Monotonicity { .. } => {
                panic!("strict subcritical scale should select consistency")
            }
        }
    }
}
