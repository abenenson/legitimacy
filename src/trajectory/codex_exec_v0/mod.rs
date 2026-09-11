//! Strict adapter for the closed Codex CLI 0.144.0 `exec --json` profile.
//!
//! The adapter proves deterministic translation relative to exact authorized
//! bytes, a private receipt, and an out-of-band trusted context. It does not
//! turn a synthetic fixture into process evidence.

mod bundle;
mod error;
mod event;
mod framing;
mod fsm;
mod lineage_sidecar;
mod mapping;
mod process_capture;
mod publication_authority;
mod receipt;
mod sanitizer;
mod source_bindings;

pub use bundle::{
    AdaptedCodexExecV0, InspectedPrivateAdapterBundleV0, InspectedShareableSanitizedBundleV0,
    PrivateAdapterBundleV0, RevalidatedPrivateAdapterBundleV0,
    RevalidatedShareableSanitizedBundleV0, TransformationReceiptV0,
};
pub use error::{AdapterErrorCodeV0, AdapterErrorV0};
pub use lineage_sidecar::{
    MAX_OWNER_PRIVATE_LINEAGE_SIDECAR_BYTES_V0, OwnerPrivateLineageSidecarV0,
};
pub use process_capture::{ProcessCaptureRequestV0, capture_codex_process_v0};
pub use publication_authority::{
    ProductionSanitizationTransactionV0, ShareableSanitizedBundleV0, sanitize_capture_v0,
};
pub use receipt::{
    ArgvBytesV0, AssertedNonceSourceV0, AssertedParentReceiptV0, CaptureManifestEntryV0,
    CaptureProfileV0, FixedSyntheticTestNonceV0, FreshExecModeV0, InodeIdentityV0,
    InputAuthorityReceiptV0, ProcessCaptureReceiptV0, ProcessTerminationV0,
    PublicDerivedReceiptProjectionV0, SanitizedDerivedCaptureReceiptV0, SyntheticFixtureReceiptV0,
    TrustedAdaptationContextV0,
};
pub use sanitizer::{
    FixedTestSanitizationMaterialV0, FixedTestSanitizedCaptureV0,
    sanitize_capture_with_fixed_test_nonce_v0,
};
pub use source_bindings::{
    CodexExecSanitizerCompiledAttestationV0, CodexExecSanitizerCompiledComponentV0,
    codex_exec_sanitizer_compiled_attestation_v0,
};

use super::{ArtifactBindingV0, artifact_digest_v0};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CodexExecSourceBindingContractV0 {
    pub identity: &'static str,
    pub framing_domain: &'static str,
    pub registered_scopes: &'static [&'static str],
}

pub const CODEX_EXEC_ADAPTER_BINDING_CONTRACT_V0: CodexExecSourceBindingContractV0 =
    CodexExecSourceBindingContractV0 {
        identity: "legitimacy.codex-exec-v0.adapter",
        framing_domain: "legitimacy.codex-exec-v0.adapter-source-manifest.v0",
        registered_scopes: &["adapter-core"],
    };
pub const CODEX_EXEC_SANITIZER_BINDING_CONTRACT_V0: CodexExecSourceBindingContractV0 =
    CodexExecSourceBindingContractV0 {
        identity: "legitimacy.codex-exec-v0.sanitizer",
        framing_domain: "legitimacy.codex-exec-v0.sanitizer-registered-source-manifest.v0",
        registered_scopes: &["adapter-core", "sanitizer"],
    };
pub const CODEX_EXEC_CLI_PUBLICATION_BINDING_CONTRACT_V0: CodexExecSourceBindingContractV0 =
    CodexExecSourceBindingContractV0 {
        identity: "legitimacy.codex-exec-v0.cli-publication",
        framing_domain: "legitimacy.codex-exec-v0.cli-publication-registered-source-manifest.v0",
        registered_scopes: &["selected-cargo-build", "normative-contract"],
    };
pub const CODEX_EXEC_FIXTURE_SPEC_BINDING_CONTRACT_V0: CodexExecSourceBindingContractV0 =
    CodexExecSourceBindingContractV0 {
        identity: "legitimacy.codex-exec-v0.fixture-spec",
        framing_domain: "legitimacy.codex-exec-v0.fixture-source-manifest.v0",
        registered_scopes: &["fixture-spec"],
    };
pub const CODEX_EXEC_CAPTURE_PRODUCER_BINDING_CONTRACT_V0: CodexExecSourceBindingContractV0 =
    CodexExecSourceBindingContractV0 {
        identity: "legitimacy.codex-exec-v0.capture-producer",
        framing_domain: "legitimacy.codex-exec-v0.capture-producer-source-manifest.v0",
        registered_scopes: &["capture-producer"],
    };

pub const CODEX_CLI_VERSION_V0: &str = "0.144.0";
pub const CODEX_SOURCE_TAG_V0: &str = "rust-v0.144.0";
pub const CODEX_SOURCE_TAG_OBJECT_SHA_V0: &str = "e0a9ff6938d85db1a7b11a693b6aa2bc31fe5a55";
pub const CODEX_SOURCE_COMMIT_SHA_V0: &str = "767822446c7a594caa19609ca435281a9ec67e0d";
pub const CODEX_EXEC_SANITIZED_THREAD_ID_DOMAIN_V0: &str =
    "legitimacy.codex-exec-v0.sanitized-thread-id.v0";

pub const MAX_CODEX_JSONL_BYTES_V0: usize = 8 * 1024 * 1024;
pub const MAX_CODEX_RECORD_BYTES_V0: usize = 512 * 1024;
pub const MAX_CODEX_RECORDS_V0: usize = 4_096;
pub const MAX_CODEX_JSON_DEPTH_V0: usize = 16;
pub const MAX_CODEX_JSON_NODES_V0: usize = 32_768;
pub const MAX_CODEX_JSON_KEYS_V0: usize = 8_192;
pub const MAX_CODEX_DECODED_STRING_BYTES_V0: usize = 384 * 1024;
pub const MAX_AUTHORITY_RECEIPT_BYTES_V0: usize = 2 * 1024 * 1024;
pub const MAX_TRUSTED_CONTEXT_BYTES_V0: usize = 64 * 1024;
pub const MAX_ADAPTER_BUNDLE_BYTES_V0: usize = 16 * 1024 * 1024;
pub const MAX_ARGV_ARGUMENTS_V0: usize = 32;
pub const MAX_ARGV_ARGUMENT_BYTES_V0: usize = 4 * 1024;
pub const MAX_ARGV_TOTAL_BYTES_V0: usize = 32 * 1024;
pub const MAX_CAPTURE_MANIFEST_ENTRIES_V0: usize = 256;

pub(super) const PROCESS_CAPTURE_ARGV_V0: &[&[u8]] = &[
    b"codex",
    b"exec",
    b"--json",
    b"--ephemeral",
    b"--ignore-user-config",
    b"--ignore-rules",
    b"--skip-git-repo-check",
    b"--sandbox",
    b"read-only",
    b"-",
];
pub(super) const PROCESS_CAPTURE_EXECUTABLE_SHA256_V0: &str =
    "sha256:901923c1808a151f6926d41d703c17ad48815662cefb1c8d832a052c44271429";
pub(super) const PROCESS_CAPTURE_RELEASE_NAME_V0: &str = "codex-x86_64-unknown-linux-musl.tar.gz";
pub(super) const PROCESS_CAPTURE_RELEASE_SHA256_V0: &str =
    "sha256:725883fc20ab4af3072829aaa0edf6d12c216238f9f7315a6656b950fb05c8bb";
pub(super) const PROCESS_CAPTURE_SIGSTORE_NAME_V0: &str =
    "codex-x86_64-unknown-linux-musl.sigstore";
pub(super) const PROCESS_CAPTURE_SIGSTORE_SHA256_V0: &str =
    "sha256:73ee5b4cb99abfce4d7a03faf7b410b5d7c869a24b856bf23a5be031e619b4cd";
pub(super) const PROCESS_CAPTURE_ARCHIVE_MEMBER_V0: &[u8] = b"codex-x86_64-unknown-linux-musl";

const SANITIZER_POLICY_V0: &[u8] = b"legitimacy.codex-exec-v0.sanitizer-policy\n\
retain=event-structure,item-ids,statuses,integers,booleans\n\
replace=thread,prose,command,output,path,todo-text\n";
const CAPTURE_PROFILE_ARTIFACT_V0: &[u8] = b"legitimacy.codex-exec-v0.capture-profile\n\
platform=unix\nmode=fresh-structured-stdin-json\nsandbox=read-only\n\
executable=fexecve-held-fd\nartifacts=held-fd-no-symlink\nworkspace=held-read-only\n";

pub fn codex_exec_adapter_binding_v0() -> ArtifactBindingV0 {
    source_bindings::adapter_binding()
}

pub fn codex_exec_sanitizer_binding_v0() -> ArtifactBindingV0 {
    source_bindings::sanitizer_binding()
}

pub fn codex_exec_cli_publication_binding_v0() -> ArtifactBindingV0 {
    source_bindings::cli_publication_binding()
}

pub fn codex_exec_sanitizer_policy_binding_v0() -> ArtifactBindingV0 {
    ArtifactBindingV0 {
        identity: "legitimacy.codex-exec-v0.sanitizer-policy".to_string(),
        version: "0".to_string(),
        hash: artifact_digest_v0(SANITIZER_POLICY_V0),
    }
}

pub fn codex_exec_fixture_spec_binding_v0() -> ArtifactBindingV0 {
    source_bindings::fixture_spec_binding()
}

pub fn codex_exec_capture_profile_binding_v0() -> ArtifactBindingV0 {
    ArtifactBindingV0 {
        identity: "legitimacy.codex-exec-v0.capture-profile".to_string(),
        version: "0".to_string(),
        hash: artifact_digest_v0(CAPTURE_PROFILE_ARTIFACT_V0),
    }
}

pub fn codex_exec_capture_producer_binding_v0() -> ArtifactBindingV0 {
    source_bindings::capture_producer_binding()
}

pub fn adapt_codex_exec_v0(
    jsonl: &[u8],
    authority: &InputAuthorityReceiptV0,
    trusted_context: &TrustedAdaptationContextV0,
) -> Result<AdaptedCodexExecV0, AdapterErrorV0> {
    bundle::adapt(jsonl, authority, trusted_context)
}

pub fn adapt_codex_exec_owned_v0(
    jsonl: Vec<u8>,
    authority: &InputAuthorityReceiptV0,
    trusted_context: &TrustedAdaptationContextV0,
) -> Result<AdaptedCodexExecV0, AdapterErrorV0> {
    bundle::adapt_owned(jsonl, authority, trusted_context)
}

pub fn codex_exec_workspace_tree_digest_v0(
    entries: &[CaptureManifestEntryV0],
) -> Result<String, AdapterErrorV0> {
    receipt::workspace::workspace_tree_digest(entries)
}
