use std::fmt;

/// Closed, attacker-independent failure vocabulary for the strict adapter.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum AdapterErrorCodeV0 {
    UnsafeInputPath,
    UnsafeOutputPath,
    InputOpen,
    InputType,
    InputSymlink,
    InputAlias,
    InputChanged,
    InputTooLarge,
    OutputSymlink,
    CrossOutputAlias,
    UnsupportedInputProfile,
    JsonFraming,
    JsonSyntax,
    JsonShape,
    JsonBudget,
    ReceiptShape,
    ReceiptMismatch,
    TrustedContextMismatch,
    UnsupportedAuthority,
    UnsupportedProfile,
    IllegalTermination,
    StreamState,
    UnsupportedRecord,
    Mapping,
    Validation,
    BundleMismatch,
    LineageSidecarShape,
    SanitizerRejected,
    OutputExists,
    OutputPublish,
    DurabilityUncertain,
    OutputIdentityUncertain,
    OutputIntegrityUncertain,
    OutputRollbackUncertain,
    UnsupportedPublicationProfile,
    EntropyUnavailable,
    PublicShareabilityDenied,
    ReservedPolicy,
    UnsupportedPlatform,
    CaptureSpawn,
    CaptureStdin,
    CaptureStdoutOverflow,
    CaptureStderrOverflow,
    CaptureTimeout,
    CaptureLiveDescendant,
    CaptureCleanup,
}

impl AdapterErrorCodeV0 {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::UnsafeInputPath => "unsafe-input-path",
            Self::UnsafeOutputPath => "unsafe-output-path",
            Self::InputOpen => "input-open",
            Self::InputType => "input-type",
            Self::InputSymlink => "input-symlink",
            Self::InputAlias => "input-alias",
            Self::InputChanged => "input-changed",
            Self::InputTooLarge => "input-too-large",
            Self::OutputSymlink => "output-symlink",
            Self::CrossOutputAlias => "cross-output-alias",
            Self::UnsupportedInputProfile => "unsupported-input-profile",
            Self::JsonFraming => "json-framing",
            Self::JsonSyntax => "json-syntax",
            Self::JsonShape => "json-shape",
            Self::JsonBudget => "json-budget",
            Self::ReceiptShape => "receipt-shape",
            Self::ReceiptMismatch => "receipt-mismatch",
            Self::TrustedContextMismatch => "trusted-context-mismatch",
            Self::UnsupportedAuthority => "unsupported-authority",
            Self::UnsupportedProfile => "unsupported-profile",
            Self::IllegalTermination => "illegal-termination",
            Self::StreamState => "stream-state",
            Self::UnsupportedRecord => "unsupported-record",
            Self::Mapping => "mapping",
            Self::Validation => "validation",
            Self::BundleMismatch => "bundle-mismatch",
            Self::LineageSidecarShape => "lineage-sidecar-shape",
            Self::SanitizerRejected => "sanitizer-rejected",
            Self::OutputExists => "output-exists",
            Self::OutputPublish => "output-publish",
            Self::DurabilityUncertain => "durability-uncertain",
            Self::OutputIdentityUncertain => "output-identity-uncertain",
            Self::OutputIntegrityUncertain => "output-integrity-uncertain",
            Self::OutputRollbackUncertain => "output-rollback-uncertain",
            Self::UnsupportedPublicationProfile => "unsupported-publication-profile",
            Self::EntropyUnavailable => "entropy-unavailable",
            Self::PublicShareabilityDenied => "public-shareability-denied",
            Self::ReservedPolicy => "reserved-policy",
            Self::UnsupportedPlatform => "unsupported-platform",
            Self::CaptureSpawn => "capture-spawn",
            Self::CaptureStdin => "capture-stdin",
            Self::CaptureStdoutOverflow => "capture-stdout-overflow",
            Self::CaptureStderrOverflow => "capture-stderr-overflow",
            Self::CaptureTimeout => "capture-timeout",
            Self::CaptureLiveDescendant => "capture-live-descendant",
            Self::CaptureCleanup => "capture-cleanup",
        }
    }
}

/// Bounded diagnostic which never contains decoded attacker-controlled text.
#[derive(Clone, Eq, PartialEq)]
pub struct AdapterErrorV0 {
    code: AdapterErrorCodeV0,
    record_index: Option<u64>,
    structural_path: Option<&'static str>,
}

impl AdapterErrorV0 {
    pub const fn from_code(code: AdapterErrorCodeV0) -> Self {
        Self::new(code)
    }

    pub(crate) const fn new(code: AdapterErrorCodeV0) -> Self {
        Self {
            code,
            record_index: None,
            structural_path: None,
        }
    }

    pub(crate) fn record(
        code: AdapterErrorCodeV0,
        record_index: usize,
        structural_path: &'static str,
    ) -> Self {
        Self {
            code,
            record_index: u64::try_from(record_index).ok(),
            structural_path: Some(structural_path),
        }
    }

    pub const fn code(&self) -> AdapterErrorCodeV0 {
        self.code
    }

    pub const fn record_index(&self) -> Option<u64> {
        self.record_index
    }

    pub const fn structural_path(&self) -> Option<&'static str> {
        self.structural_path
    }
}

impl fmt::Display for AdapterErrorV0 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.code.as_str())
    }
}

impl fmt::Debug for AdapterErrorV0 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("AdapterErrorV0")
            .field("code", &self.code)
            .field("record_index", &self.record_index)
            .field("structural_path", &self.structural_path)
            .finish()
    }
}

impl std::error::Error for AdapterErrorV0 {}

pub(crate) type AdapterResultV0<T> = Result<T, AdapterErrorV0>;
