#[derive(Clone, Copy, Debug, PartialEq)]
pub struct TwoStateCountingKernel {
    pub g: f64,
}

impl TwoStateCountingKernel {
    pub fn new(g: f64) -> Result<Self, TwoStateCountingKernelError> {
        if g.is_finite() && g > 0.0 {
            Ok(Self { g })
        } else {
            Err(TwoStateCountingKernelError::NonPositiveDiagonalParameter(g))
        }
    }

    pub fn diagonal_mass(self) -> f64 {
        1.0 / (1.0 + self.g)
    }

    pub fn off_diagonal_mass(self) -> f64 {
        self.g / (1.0 + self.g)
    }

    pub fn entry(self, x: bool, y: bool) -> f64 {
        if x == y {
            self.diagonal_mass()
        } else {
            self.off_diagonal_mass()
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TwoStateCountingKernelError {
    NonPositiveDiagonalParameter(f64),
}

pub fn operator_spectral_gap(kernel: TwoStateCountingKernel) -> f64 {
    kernel.entry(false, true) + kernel.entry(true, false)
}

pub fn two_state_counting_kernel_operator_spectral_gap_eq(
    g: f64,
) -> Result<f64, TwoStateCountingKernelError> {
    let kernel = TwoStateCountingKernel::new(g)?;
    Ok(operator_spectral_gap(kernel))
}

pub fn two_state_counting_kernel_closed_form(g: f64) -> Result<f64, TwoStateCountingKernelError> {
    TwoStateCountingKernel::new(g).map(|kernel| 2.0 * kernel.g / (1.0 + kernel.g))
}

#[cfg(test)]
mod tests {
    use super::{
        TwoStateCountingKernel, operator_spectral_gap, two_state_counting_kernel_closed_form,
        two_state_counting_kernel_operator_spectral_gap_eq,
    };

    #[test]
    fn two_state_counting_kernel_gap_matches_closed_form() {
        for g in [0.1, 0.5, 1.0, 2.5, 10.0] {
            let kernel = TwoStateCountingKernel::new(g).unwrap();
            let direct = operator_spectral_gap(kernel);
            let theorem_form = two_state_counting_kernel_operator_spectral_gap_eq(g).unwrap();
            let closed_form = two_state_counting_kernel_closed_form(g).unwrap();

            assert!((direct - closed_form).abs() < 1e-12);
            assert!((theorem_form - closed_form).abs() < 1e-12);
        }
    }
}
