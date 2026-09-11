use legitimacy::trajectory::codex_exec_v0::{
    AdapterErrorCodeV0, AdapterErrorV0, FixedSyntheticTestNonceV0, FixedTestSanitizationMaterialV0,
    InputAuthorityReceiptV0, SyntheticFixtureReceiptV0, TrustedAdaptationContextV0,
    adapt_codex_exec_v0, codex_exec_fixture_spec_binding_v0,
};
use legitimacy::{ArtifactBindingV0, artifact_digest_v0};

#[path = "codex_exec_v0/bundle_attacks.rs"]
mod bundle_attacks;
#[path = "codex_exec_v0/bundles.rs"]
mod bundles;
#[path = "codex_exec_v0/capture_attacks.rs"]
mod capture_attacks;
#[path = "codex_exec_v0/cli.rs"]
mod cli;
#[path = "codex_exec_v0/cli_errors.rs"]
mod cli_errors;
#[path = "codex_exec_v0/grammar_matrix.rs"]
mod grammar_matrix;
#[path = "codex_exec_v0/imported_declarations.rs"]
mod imported_declarations;
#[path = "codex_exec_v0/limits.rs"]
mod limits;
#[path = "codex_exec_v0/lineage_sidecar.rs"]
mod lineage_sidecar;
#[path = "codex_exec_v0/parser_fsm.rs"]
mod parser_fsm;
#[path = "codex_exec_v0/privacy.rs"]
mod privacy;
#[path = "codex_exec_v0/receipts.rs"]
mod receipts;
#[path = "codex_exec_v0/repository_object.rs"]
mod repository_object;
#[path = "codex_exec_v0/selected_repository_inputs.rs"]
mod selected_repository_inputs;
#[path = "codex_exec_v0/source_binding_registry.rs"]
mod source_binding_registry;
#[path = "codex_exec_v0/source_bindings.rs"]
mod source_bindings;

pub(crate) const COMPLETED: &[u8] =
    include_bytes!("fixtures/codex-exec-v0/legal-completed.synthetic.jsonl");
pub(crate) const FAILED: &[u8] =
    include_bytes!("fixtures/codex-exec-v0/legal-failed.synthetic.jsonl");

pub(crate) fn policy_binding() -> ArtifactBindingV0 {
    ArtifactBindingV0 {
        identity: "policy.synthetic-downstream".to_string(),
        version: "165.4-test".to_string(),
        hash: artifact_digest_v0(b"synthetic downstream policy context"),
    }
}

pub(crate) fn synthetic_authority(bytes: &[u8]) -> InputAuthorityReceiptV0 {
    InputAuthorityReceiptV0::SyntheticFixture(
        SyntheticFixtureReceiptV0::new_with_fixed_test_nonce(
            bytes,
            codex_exec_fixture_spec_binding_v0(),
            FixedSyntheticTestNonceV0::new([0x42; 32]),
        )
        .unwrap(),
    )
}

pub(crate) fn trusted(authority: &InputAuthorityReceiptV0) -> TrustedAdaptationContextV0 {
    TrustedAdaptationContextV0::new(authority.commitment(), policy_binding()).unwrap()
}

pub(crate) fn fixed_sanitization_material(byte: u8) -> FixedTestSanitizationMaterialV0 {
    FixedTestSanitizationMaterialV0::new(
        FixedSyntheticTestNonceV0::new([byte; 32]),
        FixedSyntheticTestNonceV0::new([byte.wrapping_add(1); 32]),
    )
}

pub(crate) fn adapt_fresh(
    bytes: &[u8],
) -> Result<
    legitimacy::trajectory::codex_exec_v0::AdaptedCodexExecV0,
    legitimacy::trajectory::codex_exec_v0::AdapterErrorV0,
> {
    let authority = synthetic_authority(bytes);
    adapt_codex_exec_v0(bytes, &authority, &trusted(&authority))
}

pub(crate) fn assert_adapter_error<T>(
    result: Result<T, AdapterErrorV0>,
    code: AdapterErrorCodeV0,
    record_index: Option<u64>,
    structural_path: Option<&'static str>,
) {
    let error = match result {
        Ok(_) => panic!("case must fail"),
        Err(error) => error,
    };
    assert_eq!(error.code(), code);
    assert_eq!(error.record_index(), record_index);
    assert_eq!(error.structural_path(), structural_path);
}

#[test]
fn compiled_attestation_api_is_exactly_read_only_v0() {
    source_binding_registry::attestation::assert_compiled_attestation_api_is_exactly_read_only_v0();
}

#[test]
#[serial_test::serial]
fn process_failure_kills_drains_waits_and_reaps_the_group() {
    source_binding_registry::process::assert_process_failure_kills_drains_waits_and_reaps_the_group(
    );
}

#[test]
fn ready_record_publication_is_atomic_durable_and_no_replace() {
    source_binding_registry::compiler_records::assert_ready_record_publication_is_atomic_durable_and_no_replace();
}

#[test]
fn owned_suite_scavenging_rejects_foreign_live_and_symlink_roots() {
    source_binding_registry::compiler_records::assert_owned_suite_scavenging_rejects_foreign_live_and_symlink_roots();
}

#[test]
fn compiler_protocol_fixtures_are_strict_and_deterministic() {
    source_binding_registry::compiler_protocol::assert_compiler_protocol_fixtures_are_strict_and_deterministic();
    source_binding_registry::selected_artifacts::assert_package_and_artifact_association_is_exact();
    source_binding_registry::compiler_envelope::assert_canonical_envelope_is_strict();
    source_binding_registry::release_harness::assert_release_gate_wiring_is_exact();
}

#[test]
fn ignored_maintainer_payload_cannot_mask_tracked_publication_failure() {
    source_binding_registry::publication_gate_tests::assert_ignored_maintainer_payload_cannot_mask_tracked_failure();
}

#[test]
fn selected_cfg_uses_active_atoms_and_recognized_false_grammar() {
    source_binding_registry::selected_cfg::assert_selected_cfg_uses_active_atoms_and_recognized_false_grammar();
}

#[test]
fn direct_graph_parsing_is_suffix_independent_and_fail_closed() {
    source_binding_registry::direct_graph::assert_direct_graph_parsing_is_suffix_independent_and_fail_closed();
    source_binding_registry::selected_expansion::assert_expanded_topology_fixture_is_whole_stream_and_target_separate();
}

#[test]
fn authority_allowance_contains_only_two_canonical_sites() {
    source_binding_registry::authority_surface::assert_authority_allowance_contains_only_two_canonical_sites();
}

#[test]
fn removing_either_expansion_allowance_rejects_the_baseline_fixture() {
    source_binding_registry::authority_surface::assert_removing_either_expansion_allowance_rejects_the_baseline_fixture();
}

#[test]
fn stale_compiled_binding_policy_only_fails_at_binding_comparison() {
    source_binding_registry::selected_binding::assert_stale_compiled_binding_policy_only_fails_at_binding_comparison();
}

#[test]
fn unbound_synthetic_tree_has_no_final_constructor() {
    source_binding_registry::selected_binding::assert_unbound_synthetic_tree_has_no_final_constructor();
}

#[test]
fn selected_sensitive_attack_matrix_policy_only() {
    source_binding_registry::sensitive_policy_tests::assert_selected_sensitive_attack_matrix_policy_only();
    source_binding_registry::selected_owner::assert_selected_owner_is_structural_and_graph_bound();
}

#[test]
fn frozen_base_blobs_and_dependency_closure_are_exact() {
    source_binding_registry::frozen_control::assert_frozen_base_blobs_and_dependency_closure_are_exact();
    source_binding_registry::frozen_control::assert_frozen_sibling_projection_is_exact();
    source_binding_registry::frozen_control::assert_sanitizer_structural_controls_are_live();
}

#[test]
fn downstream_selected_checkers_have_no_reopen_capability() {
    source_binding_registry::downstream::assert_downstream_selected_checkers_have_no_reopen_capability();
}

#[test]
fn downstream_coverage_equals_all_graph_and_component_keys() {
    source_binding_registry::downstream::assert_downstream_coverage_equals_all_graph_and_component_keys();
}

#[test]
fn legacy_arrays_have_exactly_two_authorized_consumers() {
    source_binding_registry::frozen_control::assert_legacy_arrays_have_exactly_two_authorized_consumers();
}

#[test]
#[ignore = "requires reviewed compiler compatibility lane"]
#[serial_test::serial]
fn selected_authority_full_tree_release_gate() {
    source_binding_registry::release_harness::run_selected_authority_full_tree_release_gate()
        .unwrap_or_else(|failure| panic!("{failure}"));
}
