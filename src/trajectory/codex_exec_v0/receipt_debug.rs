use super::*;
use std::fmt;

macro_rules! redacted_debug {
    ($type:ty, $label:literal) => {
        impl fmt::Debug for $type {
            fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str(concat!($label, " { <redacted> }"))
            }
        }
    };
}

redacted_debug!(InodeIdentityV0, "InodeIdentityV0");
redacted_debug!(ArgvBytesV0, "ArgvBytesV0");
redacted_debug!(CaptureManifestEntryV0, "CaptureManifestEntryV0");
redacted_debug!(SyntheticFixtureReceiptV0, "SyntheticFixtureReceiptV0");
redacted_debug!(ProcessCaptureReceiptV0, "ProcessCaptureReceiptV0");
redacted_debug!(
    SanitizedDerivedCaptureReceiptV0,
    "SanitizedDerivedCaptureReceiptV0"
);
redacted_debug!(TrustedAdaptationContextV0, "TrustedAdaptationContextV0");
redacted_debug!(
    PublicDerivedReceiptProjectionV0,
    "PublicDerivedReceiptProjectionV0"
);

impl fmt::Debug for InputAuthorityReceiptV0 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let authority = match self {
            Self::SyntheticFixture(_) => "synthetic-fixture",
            Self::ProcessCapture(_) => "process-capture",
            Self::SanitizedDerivedCapture(_) => "sanitized-derived-capture",
        };
        formatter
            .debug_struct("InputAuthorityReceiptV0")
            .field("authority", &authority)
            .finish_non_exhaustive()
    }
}
