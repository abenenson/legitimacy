use super::*;

impl SyntheticFixtureReceiptV0 {
    pub(super) fn validate(&self) -> AdapterResultV0<()> {
        if self.receipt_format != "legitimacy.codex-exec-v0.synthetic-fixture-receipt"
            || self.receipt_version != "0"
            || self.evidence_class != "synthetic-fixture"
            || self.raw_record_count != self.raw_capture_seal.record_count
        {
            return Err(shape());
        }
        self.emitter.validate()?;
        validate_sha256(&self.full_jsonl_digest)?;
        validate_sha256(&self.raw_capture_seal.digest)?;
        validate_binding(&self.fixture_spec_manifest)?;
        if self.fixture_spec_manifest != super::super::codex_exec_fixture_spec_binding_v0() {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptMismatch));
        }
        validate_nonce(&self.blinding_nonce_lower_hex, self.asserted_nonce_source)
    }
}

impl ProcessCaptureReceiptV0 {
    pub(super) fn validate(&self) -> AdapterResultV0<()> {
        if self.receipt_format != "legitimacy.codex-exec-v0.process-capture-receipt"
            || self.receipt_version != "0"
            || self.evidence_class != "genuine-process-capture"
            || self.asserted_nonce_source != AssertedNonceSourceV0::CaptureRandom
            || self.raw_record_count != self.raw_capture_seal.record_count
        {
            return Err(shape());
        }
        self.emitter.validate()?;
        validate_sha256(&self.executable_sha256)?;
        if self.executable_sha256 != super::super::PROCESS_CAPTURE_EXECUTABLE_SHA256_V0 {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptMismatch));
        }
        if self.executable_execution_binding != "fexecve-held-fd"
            || self.artifact_open_discipline != "held-fd-no-symlink"
            || self.workspace_execution_discipline != "held-read-only-during-exec"
        {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::UnsupportedProfile));
        }
        if self.argv.decoded()?.as_slice() != super::super::PROCESS_CAPTURE_ARGV_V0 {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::UnsupportedProfile));
        }
        if !matches!(self.stdin, ByteInputSealV0::Present { .. }) {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::UnsupportedProfile));
        }
        validate_input_seal(&self.stdin)?;
        validate_stream_seal(&self.stdout)?;
        validate_stream_seal(&self.stderr)?;
        validate_sha256(&self.raw_capture_seal.digest)?;
        validate_binding(&self.capture_tool.identity)?;
        validate_sha256(&self.capture_tool.file_sha256)?;
        if self.capture_tool.identity != super::super::codex_exec_capture_producer_binding_v0() {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptMismatch));
        }
        validate_binding(&self.capture_profile_artifact)?;
        if self.capture_profile_artifact != super::super::codex_exec_capture_profile_binding_v0() {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::UnsupportedProfile));
        }
        if self.workspace_manifest.len() > MAX_CAPTURE_MANIFEST_ENTRIES_V0 {
            return Err(shape());
        }
        super::workspace::validate_order(&self.workspace_manifest)?;
        if self.executable_inode == self.capture_tool.inode
            || self.workspace_manifest.iter().any(|entry| {
                entry.inode == self.executable_inode || entry.inode == self.capture_tool.inode
            })
        {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptMismatch));
        }
        validate_sha256(&self.workspace_tree_digest)?;
        if self.workspace_tree_digest
            != super::workspace::workspace_tree_digest(&self.workspace_manifest)?
        {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptMismatch));
        }
        if self.release_asset.name != super::super::PROCESS_CAPTURE_RELEASE_NAME_V0
            || self.release_asset.sha256 != super::super::PROCESS_CAPTURE_RELEASE_SHA256_V0
            || self.sigstore_bundle.name != super::super::PROCESS_CAPTURE_SIGSTORE_NAME_V0
            || self.sigstore_bundle.sha256 != super::super::PROCESS_CAPTURE_SIGSTORE_SHA256_V0
            || !matches!(
                self.sigstore_verification.as_str(),
                "verified-sigstore-rekor" | "bundle-present-unverified"
            )
        {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptMismatch));
        }
        validate_nonce(
            &self.blinding_nonce_lower_hex,
            AssertedNonceSourceV0::CaptureRandom,
        )?;
        validate_termination_domain(&self.termination)
    }
}

impl SanitizedDerivedCaptureReceiptV0 {
    pub(super) fn validate(&self) -> AdapterResultV0<()> {
        if self.receipt_format != "legitimacy.codex-exec-v0.sanitized-derived-capture-receipt"
            || self.receipt_version != "0"
            || self.evidence_class != "sanitized-derived-capture"
            || !matches!(
                self.asserted_origin_evidence_class.as_str(),
                "synthetic-fixture" | "genuine-process-capture"
            )
            || !matches!(
                (
                    self.asserted_origin_evidence_class.as_str(),
                    self.asserted_parent_receipt,
                    self.asserted_nonce_source
                ),
                (
                    "synthetic-fixture",
                    AssertedParentReceiptV0::AssertedParentReceiptSyntheticFixtureCaptureRandom
                        | AssertedParentReceiptV0::AssertedParentReceiptSyntheticFixtureFixedSyntheticTest,
                    _
                ) | (
                    "genuine-process-capture",
                    AssertedParentReceiptV0::AssertedParentReceiptProcessCaptureCaptureRandom,
                    AssertedNonceSourceV0::CaptureRandom
                )
            )
        {
            return Err(shape());
        }
        for digest in [
            &self.parent_receipt_commitment,
            &self.parent_full_jsonl_digest,
            &self.parent_raw_capture_seal.digest,
            &self.derived_full_jsonl_digest,
            &self.derived_raw_capture_seal.digest,
        ] {
            validate_sha256(digest)?;
        }
        validate_binding(&self.sanitizer_policy)?;
        validate_binding(&self.sanitizer_artifact)?;
        if self.sanitizer_policy != super::super::codex_exec_sanitizer_policy_binding_v0()
            || self.sanitizer_artifact != super::super::codex_exec_sanitizer_binding_v0()
        {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptMismatch));
        }
        validate_nonce(&self.blinding_nonce_lower_hex, self.asserted_nonce_source)
    }
}

pub(super) fn validate_binding(binding: &ArtifactBindingV0) -> AdapterResultV0<()> {
    validate_name(&binding.identity)?;
    if binding.version.is_empty()
        || binding.version.len() > 64
        || !binding.version.bytes().all(|byte| {
            matches!(
                byte,
                b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'.' | b'-' | b'_' | b'+'
            )
        })
    {
        return Err(shape());
    }
    validate_sha256(&binding.hash)
}

pub(super) fn validate_name(value: &str) -> AdapterResultV0<()> {
    if value.is_empty()
        || value.len() > 128
        || !value.bytes().enumerate().all(|(index, byte)| match byte {
            b'a'..=b'z' | b'0'..=b'9' => true,
            b'.' | b'-' | b'_' => index > 0,
            _ => false,
        })
    {
        return Err(shape());
    }
    Ok(())
}

pub(super) fn validate_sha256(value: &str) -> AdapterResultV0<()> {
    let valid = value
        .strip_prefix("sha256:")
        .is_some_and(|hex| hex.len() == 64 && hex.bytes().all(is_lower_hex));
    if !valid {
        return Err(shape());
    }
    Ok(())
}

fn validate_nonce(value: &str, provenance: AssertedNonceSourceV0) -> AdapterResultV0<()> {
    if value.len() != 64
        || !value.bytes().all(is_lower_hex)
        || (provenance == AssertedNonceSourceV0::CaptureRandom
            && value.bytes().all(|byte| byte == b'0'))
    {
        return Err(shape());
    }
    Ok(())
}

fn validate_input_seal(value: &ByteInputSealV0) -> AdapterResultV0<()> {
    match value {
        ByteInputSealV0::Absent => Ok(()),
        ByteInputSealV0::Present { sha256, .. } => validate_sha256(sha256),
    }
}

fn validate_stream_seal(value: &ByteStreamSealV0) -> AdapterResultV0<()> {
    validate_sha256(&value.sha256)
}

fn validate_termination_domain(value: &ProcessTerminationV0) -> AdapterResultV0<()> {
    match value {
        ProcessTerminationV0::Exited { code } if *code <= 125 => Ok(()),
        ProcessTerminationV0::Signaled { signal, .. } if (1..=64).contains(signal) => Ok(()),
        ProcessTerminationV0::Exited { .. } | ProcessTerminationV0::Signaled { .. } => {
            Err(AdapterErrorV0::new(AdapterErrorCodeV0::IllegalTermination))
        }
    }
}

fn is_lower_hex(byte: u8) -> bool {
    byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)
}

fn shape() -> AdapterErrorV0 {
    AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptShape)
}
