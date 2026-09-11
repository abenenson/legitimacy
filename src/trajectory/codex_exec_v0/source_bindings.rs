use super::{
    ArtifactBindingV0, CODEX_EXEC_ADAPTER_BINDING_CONTRACT_V0,
    CODEX_EXEC_CAPTURE_PRODUCER_BINDING_CONTRACT_V0,
    CODEX_EXEC_CLI_PUBLICATION_BINDING_CONTRACT_V0, CODEX_EXEC_FIXTURE_SPEC_BINDING_CONTRACT_V0,
    CODEX_EXEC_SANITIZER_BINDING_CONTRACT_V0, CodexExecSourceBindingContractV0,
};
use crate::trajectory::framed_sha256;
use sha2::{Digest, Sha256};

const SANITIZER_COMPILED_ATTESTATION_IDENTITY_V0: &str =
    "legitimacy.codex-exec-v0.sanitizer-compiled-attestation";

/// One read-only component observation from the compiled sanitizer registry.
///
/// This is a supported additive SemVer surface. Version 0 never changes its
/// representation or meaning; an incompatible schema requires a new
/// versioned type and function.
pub struct CodexExecSanitizerCompiledComponentV0 {
    component_key: &'static str,
    byte_length: u64,
    sha256: [u8; 32],
}

impl CodexExecSanitizerCompiledComponentV0 {
    pub fn component_key(&self) -> &'static str {
        self.component_key
    }

    pub fn byte_length(&self) -> u64 {
        self.byte_length
    }

    pub fn sha256(&self) -> [u8; 32] {
        self.sha256
    }
}

/// Read-only evidence computed from the sanitizer bytes compiled into this rlib.
///
/// This is a supported additive SemVer surface. Version 0 never changes its
/// representation or meaning; an incompatible schema requires a new
/// versioned type and function.
pub struct CodexExecSanitizerCompiledAttestationV0 {
    schema_identity: &'static str,
    schema_version: u16,
    components: Box<[CodexExecSanitizerCompiledComponentV0]>,
    aggregate: ArtifactBindingV0,
}

impl CodexExecSanitizerCompiledAttestationV0 {
    pub fn schema_identity(&self) -> &'static str {
        self.schema_identity
    }

    pub fn schema_version(&self) -> u16 {
        self.schema_version
    }

    pub fn components(&self) -> &[CodexExecSanitizerCompiledComponentV0] {
        &self.components
    }

    pub fn aggregate(&self) -> &ArtifactBindingV0 {
        &self.aggregate
    }
}

/// Observes the ordered sanitizer component metadata compiled into this rlib.
///
/// The returned value exposes identifiers, lengths, and digests, never source
/// bytes or publication authority. This is a supported additive SemVer
/// surface. Version 0 never changes; an incompatible schema requires a new
/// versioned type and function.
pub fn codex_exec_sanitizer_compiled_attestation_v0() -> CodexExecSanitizerCompiledAttestationV0 {
    let components = ADAPTER_CORE_SOURCES_V0
        .iter()
        .chain(SANITIZER_ONLY_SOURCES_V0)
        .map(
            |(component_key, bytes)| CodexExecSanitizerCompiledComponentV0 {
                component_key,
                byte_length: u64::try_from(bytes.len())
                    .expect("compiled component length must fit in u64"),
                sha256: Sha256::digest(bytes).into(),
            },
        )
        .collect::<Vec<_>>()
        .into_boxed_slice();
    CodexExecSanitizerCompiledAttestationV0 {
        schema_identity: SANITIZER_COMPILED_ATTESTATION_IDENTITY_V0,
        schema_version: 0,
        components,
        aggregate: sanitizer_binding(),
    }
}

const ADAPTER_CORE_SOURCES_V0: &[(&str, &[u8])] = &[
    (
        "src/trajectory/codex_exec_v0/source_bindings.rs",
        include_bytes!("source_bindings.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/bundle.rs",
        include_bytes!("bundle.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/bundle_wire.rs",
        include_bytes!("bundle_wire.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/error.rs",
        include_bytes!("error.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/event.rs",
        include_bytes!("event.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/event_wire.rs",
        include_bytes!("event_wire.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/framing.rs",
        include_bytes!("framing.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/fsm.rs",
        include_bytes!("fsm.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/mapping.rs",
        include_bytes!("mapping.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/mod.rs",
        include_bytes!("mod.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/process_capture.rs",
        include_bytes!("process_capture.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/process_capture_cleanup.rs",
        include_bytes!("process_capture_cleanup.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/process_capture_output.rs",
        include_bytes!("process_capture_output.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/process_capture_platform.rs",
        include_bytes!("process_capture_platform.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/process_capture_signal.rs",
        include_bytes!("process_capture_signal.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/process_capture_supervision.rs",
        include_bytes!("process_capture_supervision.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/process_capture_supervisor.rs",
        include_bytes!("process_capture_supervisor.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/receipt.rs",
        include_bytes!("receipt.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/receipt_canonical.rs",
        include_bytes!("receipt_canonical.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/receipt_context.rs",
        include_bytes!("receipt_context.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/receipt_debug.rs",
        include_bytes!("receipt_debug.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/receipt_hex.rs",
        include_bytes!("receipt_hex.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/receipt_nonce.rs",
        include_bytes!("receipt_nonce.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/receipt_validate.rs",
        include_bytes!("receipt_validate.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/receipt_wire.rs",
        include_bytes!("receipt_wire.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/receipt_workspace.rs",
        include_bytes!("receipt_workspace.rs"),
    ),
    ("src/trajectory/mod.rs", include_bytes!("../mod.rs")),
    (
        "src/trajectory/duplicate_json.rs",
        include_bytes!("../duplicate_json.rs"),
    ),
    (
        "src/trajectory/canonical.rs",
        include_bytes!("../canonical.rs"),
    ),
    (
        "src/trajectory/validation.rs",
        include_bytes!("../validation.rs"),
    ),
    (
        "src/trajectory/interchange.rs",
        include_bytes!("../interchange.rs"),
    ),
];

const SANITIZER_ONLY_SOURCES_V0: &[(&str, &[u8])] = &[
    (
        "src/trajectory/codex_exec_v0/sanitizer.rs",
        include_bytes!("sanitizer.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/sanitizer_jwt.rs",
        include_bytes!("sanitizer_jwt.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/publication_authority.rs",
        include_bytes!("publication_authority.rs"),
    ),
    (
        "src/trajectory/codex_exec_v0/lineage_sidecar.rs",
        include_bytes!("lineage_sidecar.rs"),
    ),
];

const CLI_SELECTED_BUILD_CONTRACT_V0: &[(&str, &[u8])] = &[(
    "tests/fixtures/codex-exec-v0/adapter-build-input.json",
    include_bytes!("../../../tests/fixtures/codex-exec-v0/adapter-build-input.json"),
)];

const FIXTURE_SPEC_SOURCES_V0: &[(&str, &[u8])] = &[(
    "tests/fixtures/codex-exec-v0/source-manifest.json",
    include_bytes!("../../../tests/fixtures/codex-exec-v0/source-manifest.json"),
)];

const CAPTURE_PRODUCER_SOURCES_V0: &[(&str, &[u8])] = &[(
    "src/bin/legitimacy-codex-capture-v0.rs",
    include_bytes!("../../bin/legitimacy-codex-capture-v0.rs"),
)];

pub(super) fn adapter_binding() -> ArtifactBindingV0 {
    binding_from_registries(
        &CODEX_EXEC_ADAPTER_BINDING_CONTRACT_V0,
        &[ADAPTER_CORE_SOURCES_V0],
    )
}

pub(super) fn sanitizer_binding() -> ArtifactBindingV0 {
    binding_from_registries(
        &CODEX_EXEC_SANITIZER_BINDING_CONTRACT_V0,
        &[ADAPTER_CORE_SOURCES_V0, SANITIZER_ONLY_SOURCES_V0],
    )
}

pub(super) fn cli_publication_binding() -> ArtifactBindingV0 {
    binding_from_registries(
        &CODEX_EXEC_CLI_PUBLICATION_BINDING_CONTRACT_V0,
        &[CLI_SELECTED_BUILD_CONTRACT_V0],
    )
}

pub(super) fn fixture_spec_binding() -> ArtifactBindingV0 {
    binding_from_registries(
        &CODEX_EXEC_FIXTURE_SPEC_BINDING_CONTRACT_V0,
        &[FIXTURE_SPEC_SOURCES_V0],
    )
}

pub(super) fn capture_producer_binding() -> ArtifactBindingV0 {
    binding_from_registries(
        &CODEX_EXEC_CAPTURE_PRODUCER_BINDING_CONTRACT_V0,
        &[ADAPTER_CORE_SOURCES_V0, CAPTURE_PRODUCER_SOURCES_V0],
    )
}

fn binding_from_registries(
    contract: &CodexExecSourceBindingContractV0,
    registries: &[&[(&str, &[u8])]],
) -> ArtifactBindingV0 {
    let components = registries
        .iter()
        .flat_map(|registry| registry.iter())
        .flat_map(|(path, bytes)| [path.as_bytes(), *bytes])
        .collect::<Vec<_>>();
    ArtifactBindingV0 {
        identity: contract.identity.to_string(),
        version: "0".to_string(),
        hash: framed_sha256(contract.framing_domain, &components),
    }
}
