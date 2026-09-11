use super::{AdapterErrorCodeV0, AdapterErrorV0, AdapterResultV0};
use serde::Serialize;
use std::fmt;

pub struct FixedSyntheticTestNonceV0([u8; 32]);

impl FixedSyntheticTestNonceV0 {
    pub const fn new(bytes: [u8; 32]) -> Self {
        Self(bytes)
    }

    pub(crate) fn into_material(self) -> NonceMaterialV0 {
        NonceMaterialV0 {
            asserted_source: AssertedNonceSourceV0::FixedSyntheticTest,
            bytes: self.0,
        }
    }

    pub(crate) const fn bytes(&self) -> &[u8; 32] {
        &self.0
    }
}

impl fmt::Debug for FixedSyntheticTestNonceV0 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("FixedSyntheticTestNonceV0 { <redacted> }")
    }
}

#[derive(Clone, Copy, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum AssertedNonceSourceV0 {
    CaptureRandom,
    FixedSyntheticTest,
}

impl AssertedNonceSourceV0 {
    pub(crate) const fn label(self) -> &'static str {
        match self {
            Self::CaptureRandom => "capture-random",
            Self::FixedSyntheticTest => "fixed-synthetic-test",
        }
    }
}

pub(crate) struct NonceMaterialV0 {
    asserted_source: AssertedNonceSourceV0,
    bytes: [u8; 32],
}

impl NonceMaterialV0 {
    pub(crate) fn capture_random() -> AdapterResultV0<Self> {
        #[cfg(not(target_os = "linux"))]
        {
            Err(AdapterErrorV0::new(AdapterErrorCodeV0::UnsupportedPlatform))
        }
        #[cfg(target_os = "linux")]
        {
            let mut bytes = [0u8; 32];
            fill_random(&mut bytes, |target| {
                rustix::rand::getrandom(target, rustix::rand::GetRandomFlags::empty())
                    .map_err(|error: rustix::io::Errno| error.raw_os_error())
            })?;
            Ok(Self {
                asserted_source: AssertedNonceSourceV0::CaptureRandom,
                bytes,
            })
        }
    }

    pub(crate) const fn asserted_source(&self) -> AssertedNonceSourceV0 {
        self.asserted_source
    }

    pub(crate) const fn bytes(&self) -> &[u8; 32] {
        &self.bytes
    }
}

#[cfg(target_os = "linux")]
fn fill_random(
    output: &mut [u8; 32],
    mut read: impl FnMut(&mut [u8]) -> Result<usize, i32>,
) -> AdapterResultV0<()> {
    let mut offset = 0;
    while offset < output.len() {
        match read(&mut output[offset..]) {
            Ok(0) => return Err(AdapterErrorV0::new(AdapterErrorCodeV0::EntropyUnavailable)),
            Ok(length) if length <= output.len() - offset => offset += length,
            Ok(_) => return Err(AdapterErrorV0::new(AdapterErrorCodeV0::EntropyUnavailable)),
            Err(code) if code == rustix::io::Errno::INTR.raw_os_error() => {}
            Err(_) => return Err(AdapterErrorV0::new(AdapterErrorCodeV0::EntropyUnavailable)),
        }
    }
    if output.iter().all(|byte| *byte == 0) {
        return Err(AdapterErrorV0::new(AdapterErrorCodeV0::EntropyUnavailable));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg(target_os = "linux")]
    fn entropy_fill_handles_partial_interrupted_and_terminal_failures() {
        let mut output = [0u8; 32];
        let mut calls = 0;
        fill_random(&mut output, |target| {
            calls += 1;
            if calls == 1 {
                return Err(rustix::io::Errno::INTR.raw_os_error());
            }
            let length = target.len().min(3);
            target[..length].fill(0x5a);
            Ok(length)
        })
        .unwrap();
        assert_eq!(output, [0x5a; 32]);
        assert!(calls > 10);

        for result in [Ok(0), Err(rustix::io::Errno::IO.raw_os_error())] {
            assert_eq!(
                fill_random(&mut [0u8; 32], |_| result).unwrap_err().code(),
                AdapterErrorCodeV0::EntropyUnavailable
            );
        }
        assert_eq!(
            fill_random(&mut [0u8; 32], |_| {
                Err(rustix::io::Errno::NOSYS.raw_os_error())
            })
            .unwrap_err()
            .code(),
            AdapterErrorCodeV0::EntropyUnavailable
        );
        assert_eq!(
            fill_random(&mut [0u8; 32], |target| Ok(target.len()))
                .unwrap_err()
                .code(),
            AdapterErrorCodeV0::EntropyUnavailable
        );
        assert_eq!(
            fill_random(&mut [0u8; 32], |target| Ok(target.len() + 1))
                .unwrap_err()
                .code(),
            AdapterErrorCodeV0::EntropyUnavailable,
            "an unavailable or nonconforming syscall wrapper must fail closed"
        );
        assert!(NonceMaterialV0::capture_random().is_ok());
    }
}
