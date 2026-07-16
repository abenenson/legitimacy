const HALF: f64 = 0.5;

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct ConcreteBSCNoisyCStarCalibration {
    pub noise: f64,
    pub target_cv: f64,
    pub tolerance: f64,
}

impl ConcreteBSCNoisyCStarCalibration {
    pub fn new(noise: f64, target_cv: f64, tolerance: f64) -> Result<Self, BscCalibrationError> {
        if !(noise.is_finite() && (0.0..HALF).contains(&noise)) {
            return Err(BscCalibrationError::NoiseOutOfRange(noise));
        }
        if !(target_cv.is_finite() && target_cv > 0.0 && target_cv < std::f64::consts::LN_2) {
            return Err(BscCalibrationError::TargetOutsideReachableRange(target_cv));
        }
        if !(tolerance.is_finite() && tolerance > 0.0) {
            return Err(BscCalibrationError::InvalidTolerance(tolerance));
        }

        let calibration = Self {
            noise,
            target_cv,
            tolerance,
        };
        if !calibration.capacity_matches_target() {
            return Err(BscCalibrationError::CapacityMismatch {
                noise,
                capacity: calibration.capacity(),
                target_cv,
                tolerance,
            });
        }
        Ok(calibration)
    }

    pub fn from_target_cv(target_cv: f64, tolerance: f64) -> Result<Self, BscCalibrationError> {
        if !(target_cv.is_finite() && target_cv > 0.0 && target_cv < std::f64::consts::LN_2) {
            return Err(BscCalibrationError::TargetOutsideReachableRange(target_cv));
        }
        if !(tolerance.is_finite() && tolerance > 0.0) {
            return Err(BscCalibrationError::InvalidTolerance(tolerance));
        }

        let mut low = 0.0;
        let mut high = HALF;
        for _ in 0..128 {
            let mid = (low + high) / 2.0;
            let capacity = bsc_channel_capacity(mid);
            if (capacity - target_cv).abs() <= tolerance {
                return Ok(Self {
                    noise: mid,
                    target_cv,
                    tolerance,
                });
            }
            if capacity > target_cv {
                low = mid;
            } else {
                high = mid;
            }
        }

        let noise = (low + high) / 2.0;
        Self::new(noise, target_cv, tolerance)
    }

    pub fn capacity(&self) -> f64 {
        bsc_channel_capacity(self.noise)
    }

    pub fn capacity_matches_target(&self) -> bool {
        (self.capacity() - self.target_cv).abs() <= self.tolerance
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum BscCalibrationError {
    NoiseOutOfRange(f64),
    TargetOutsideReachableRange(f64),
    InvalidTolerance(f64),
    CapacityMismatch {
        noise: f64,
        capacity: f64,
        target_cv: f64,
        tolerance: f64,
    },
}

pub fn binary_entropy(eta: f64) -> f64 {
    if eta <= 0.0 || eta >= 1.0 {
        return 0.0;
    }

    -eta * eta.ln() - (1.0 - eta) * (1.0 - eta).ln()
}

pub fn bsc_channel_capacity(eta: f64) -> f64 {
    std::f64::consts::LN_2 - binary_entropy(eta)
}

pub fn bsc_channel_capacity_bits(eta: f64) -> f64 {
    bsc_channel_capacity(eta) / std::f64::consts::LN_2
}

pub fn concrete_half_bsc_noisy_c_star_calibration()
-> Result<ConcreteBSCNoisyCStarCalibration, BscCalibrationError> {
    ConcreteBSCNoisyCStarCalibration::from_target_cv(0.5, 1e-12)
}

#[cfg(test)]
mod tests {
    use super::{
        binary_entropy, bsc_channel_capacity, bsc_channel_capacity_bits,
        concrete_half_bsc_noisy_c_star_calibration,
    };

    #[test]
    fn bsc_capacity_is_log_two_minus_binary_entropy() {
        let eta = 0.1;
        let expected = std::f64::consts::LN_2 - binary_entropy(eta);

        assert!((bsc_channel_capacity(eta) - expected).abs() < 1e-12);
        assert!((bsc_channel_capacity_bits(eta) - expected / std::f64::consts::LN_2).abs() < 1e-12);
    }

    #[test]
    fn concrete_half_bsc_noisy_calibration_hits_half_cv() {
        let calibration = concrete_half_bsc_noisy_c_star_calibration().unwrap();

        assert!(calibration.noise > 0.0);
        assert!(calibration.noise < 0.5);
        assert!(calibration.capacity_matches_target());
        assert!((calibration.capacity() - 0.5).abs() <= 1e-12);
    }
}
