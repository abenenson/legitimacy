use super::validate::{validate_binding, validate_sha256};
use super::*;

const RESERVED_POLICY_NAMESPACES_V0: &[&str] = &[
    "legitimacy.codex-exec-v0.",
    "legitimacy.trajectory.",
    "derivation.codex-exec-v0.",
];

impl TrustedAdaptationContextV0 {
    pub fn new(
        expected_authority_commitment: String,
        downstream_governance_policy: ArtifactBindingV0,
    ) -> AdapterResultV0<Self> {
        validate_sha256(&expected_authority_commitment)?;
        validate_binding(&downstream_governance_policy)?;
        validate_policy_identity(&downstream_governance_policy.identity)?;
        Ok(Self {
            context_format: "legitimacy.codex-exec-v0.trusted-adaptation-context".to_string(),
            context_version: "0".to_string(),
            expected_authority_commitment,
            downstream_governance_policy,
        })
    }

    pub fn from_json_slice(input: &[u8]) -> AdapterResultV0<Self> {
        wire::decode_trusted_context(input)
    }

    pub fn expected_authority_commitment(&self) -> &str {
        &self.expected_authority_commitment
    }

    pub fn downstream_governance_policy(&self) -> &ArtifactBindingV0 {
        &self.downstream_governance_policy
    }
}

pub(super) fn validate_policy_identity(identity: &str) -> AdapterResultV0<()> {
    if RESERVED_POLICY_NAMESPACES_V0
        .iter()
        .any(|prefix| identity.starts_with(prefix))
    {
        return Err(AdapterErrorV0::new(AdapterErrorCodeV0::ReservedPolicy));
    }
    Ok(())
}
