use super::source_bindings::{
    BUILD_INPUT_PATH, canonical_build_input, cli_selected_build_paths, cli_test_only_rust_paths,
};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;

// Exact source bindings are the authority for the reviewed adapter route. The
// structural checks below expose selected, security-relevant regression facts;
// they are not a whole-program Rust capability or call-graph analysis.

const EXPECTED_RELEVANT_TEST_RUST_SOURCES: &[&str] = &[
    "cli/trajectory/linux_path_tests.rs",
    "cli/trajectory/linux_output_set_tests.rs",
    "cli/trajectory/linux_output_tests.rs",
    "cli/trajectory/linux_output_transaction_tests.rs",
    "cli/trajectory/linux_output_transaction_phase_tests.rs",
    "tests/codex_exec_v0.rs",
    "tests/codex_process_capture_cli_v0.rs",
    "src/trajectory/codex_exec_v0/process_capture_platform_tests.rs",
    "src/trajectory/codex_exec_v0/process_capture_signal_tests.rs",
    "src/trajectory/codex_exec_v0/process_capture_supervision_tests.rs",
    "tests/codex_exec_v0/bundle_attacks.rs",
    "tests/codex_exec_v0/bundles.rs",
    "tests/codex_exec_v0/capture_attacks.rs",
    "tests/codex_exec_v0/cli.rs",
    "tests/codex_exec_v0/cli_errors.rs",
    "tests/codex_exec_v0/grammar_matrix.rs",
    "tests/codex_exec_v0/imported_declarations.rs",
    "tests/codex_exec_v0/limits.rs",
    "tests/codex_exec_v0/lineage_sidecar.rs",
    "tests/codex_exec_v0/parser_fsm.rs",
    "tests/codex_exec_v0/privacy.rs",
    "tests/codex_exec_v0/receipts.rs",
    "tests/codex_exec_v0/repository_object.rs",
    "tests/codex_exec_v0/selected_repository_inputs.rs",
    "tests/codex_exec_v0/source_binding_registry.rs",
    "tests/codex_exec_v0/source_binding_registry_attestation.rs",
    "tests/codex_exec_v0/source_binding_registry_authority_surface.rs",
    "tests/codex_exec_v0/source_binding_registry_compiler_envelope.rs",
    "tests/codex_exec_v0/source_binding_registry_compiler_records.rs",
    "tests/codex_exec_v0/source_binding_registry_compiler_protocol.rs",
    "tests/codex_exec_v0/source_binding_registry_direct_graph.rs",
    "tests/codex_exec_v0/source_binding_registry_downstream.rs",
    "tests/codex_exec_v0/source_binding_registry_frozen_control.rs",
    "tests/codex_exec_v0/source_binding_registry_process.rs",
    "tests/codex_exec_v0/source_binding_registry_release_harness.rs",
    "tests/codex_exec_v0/source_binding_registry_release_lifecycle.rs",
    "tests/codex_exec_v0/source_binding_registry_selected_cfg.rs",
    "tests/codex_exec_v0/source_binding_registry_selected_expansion.rs",
    "tests/codex_exec_v0/source_binding_registry_selected_final_closure.rs",
    "tests/codex_exec_v0/source_binding_registry_selected_owner.rs",
    "tests/codex_exec_v0/source_binding_registry_build_program_verification.rs",
    "tests/codex_exec_v0/source_binding_registry_build_route_tests.rs",
    "tests/codex_exec_v0/source_binding_registry_normative_contract_support.rs",
    "tests/codex_exec_v0/source_binding_registry_normative_contract_tests.rs",
    "tests/codex_exec_v0/source_binding_registry_inventory_support.rs",
    "tests/codex_exec_v0/source_binding_registry_paired_output_mutations.rs",
    "tests/codex_exec_v0/source_binding_registry_publication_gate_tests.rs",
    "tests/codex_exec_v0/source_binding_registry_publication_route_tests.rs",
    "tests/codex_exec_v0/source_binding_registry_route_bindings.rs",
    "tests/codex_exec_v0/source_binding_registry_route_verification.rs",
    "tests/codex_exec_v0/source_binding_registry_route_publication.rs",
    "tests/codex_exec_v0/source_binding_registry_route_order.rs",
    "tests/codex_exec_v0/source_binding_registry_selected_artifacts.rs",
    "tests/codex_exec_v0/source_binding_registry_selected_binding.rs",
    "tests/codex_exec_v0/source_binding_registry_selected_binding_tests.rs",
    "tests/codex_exec_v0/source_binding_registry_selected_closure.rs",
    "tests/codex_exec_v0/source_binding_registry_selected_closure_tests.rs",
    "tests/codex_exec_v0/source_binding_registry_module_graph.rs",
    "tests/codex_exec_v0/source_binding_registry_sensitive_collectors.rs",
    "tests/codex_exec_v0/source_binding_registry_sensitive_shapes.rs",
    "tests/codex_exec_v0/source_binding_registry_sensitive_policy_tests.rs",
    "tests/codex_exec_v0/source_binding_registry_sensitive_surface_tests.rs",
    "tests/codex_exec_v0/source_binding_registry_sensitive_verification.rs",
    "tests/codex_exec_v0/source_binding_registry_single_output_mutations.rs",
    "tests/codex_exec_v0/source_binding_registry_sanitizer_syntax.rs",
    "tests/codex_exec_v0/source_binding_registry_syntax_support.rs",
    "tests/codex_exec_v0/source_bindings.rs",
    "tests/codex_exec_v0/frozen_control_v0/frozen_manual_paths.rs",
    "tests/codex_exec_v0/frozen_control_v0/mod.rs",
    "tests/codex_exec_v0/support/selected_authority_compiler_proxy.rs",
    "tests/codex_exec_v0/support/selected_authority_git_answer.rs",
    "tests/codex_exec_v0/support/selected_authority_rlib_probe.rs",
];

#[path = "source_binding_registry_inventory_support.rs"]
mod inventory_support;
#[path = "source_binding_registry_module_graph.rs"]
mod module_graph;
#[path = "source_binding_registry_paired_output_mutations.rs"]
mod paired_output_mutations;
#[path = "source_binding_registry_route_bindings.rs"]
mod route_bindings;
#[path = "source_binding_registry_route_order.rs"]
mod route_order;
#[path = "source_binding_registry_route_publication.rs"]
mod route_publication;
#[path = "source_binding_registry_route_verification.rs"]
mod route_verification;
#[path = "source_binding_registry_sanitizer_syntax.rs"]
mod sanitizer_syntax;
#[path = "source_binding_registry_selected_artifacts.rs"]
pub(crate) mod selected_artifacts;
#[path = "source_binding_registry_selected_binding.rs"]
pub(crate) mod selected_binding;
#[path = "source_binding_registry_selected_closure.rs"]
mod selected_closure;
#[path = "source_binding_registry_selected_closure_tests.rs"]
mod selected_closure_tests;
#[path = "source_binding_registry_sensitive_collectors.rs"]
mod sensitive_collectors;
#[path = "source_binding_registry_sensitive_policy_tests.rs"]
pub(crate) mod sensitive_policy_tests;
#[path = "source_binding_registry_sensitive_shapes.rs"]
mod sensitive_shapes;
#[path = "source_binding_registry_sensitive_verification.rs"]
mod sensitive_verification;
#[path = "source_binding_registry_single_output_mutations.rs"]
mod single_output_mutations;
#[path = "source_binding_registry_syntax_support.rs"]
mod syntax_support;

use inventory_support::*;
use paired_output_mutations::*;
use route_bindings::*;
use route_order::*;
use route_publication::*;
use route_verification::*;
use sanitizer_syntax::*;
use selected_artifacts::*;
use selected_closure::*;
use sensitive_collectors::*;
use sensitive_shapes::*;
use sensitive_verification::*;
use single_output_mutations::*;
use syntax_support::*;

pub(super) fn connected_canonical_build_input() -> serde_json::Value {
    canonical_build_input_value()
}

pub(super) fn connected_selected_cargo_messages(
    root: &Path,
) -> Result<&'static [serde_json::Value], &'static str> {
    selected_cargo_messages(root).map_err(|_| "build-route")
}

#[path = "source_binding_registry_build_program_verification.rs"]
mod build_program_verification;
use build_program_verification::*;
#[path = "source_binding_registry_attestation.rs"]
pub(crate) mod attestation;
#[path = "source_binding_registry_authority_surface.rs"]
pub(crate) mod authority_surface;
#[path = "source_binding_registry_build_route_tests.rs"]
mod build_route_tests;
#[path = "source_binding_registry_compiler_envelope.rs"]
pub(crate) mod compiler_envelope;
#[path = "source_binding_registry_compiler_protocol.rs"]
pub(crate) mod compiler_protocol;
#[path = "source_binding_registry_compiler_records.rs"]
pub(crate) mod compiler_records;
#[path = "source_binding_registry_direct_graph.rs"]
pub(crate) mod direct_graph;
#[path = "source_binding_registry_downstream.rs"]
pub(crate) mod downstream;
#[path = "source_binding_registry_frozen_control.rs"]
pub(crate) mod frozen_control;
#[path = "source_binding_registry_process.rs"]
pub(crate) mod process;
#[path = "source_binding_registry_publication_gate_tests.rs"]
pub(crate) mod publication_gate_tests;
#[path = "source_binding_registry_release_harness.rs"]
pub(crate) mod release_harness;
#[path = "source_binding_registry_selected_cfg.rs"]
pub(crate) mod selected_cfg;
#[path = "source_binding_registry_selected_expansion.rs"]
pub(crate) mod selected_expansion;
#[path = "source_binding_registry_selected_owner.rs"]
pub(crate) mod selected_owner;
pub(super) use build_route_tests::dep_info_inputs;
#[path = "source_binding_registry_normative_contract_support.rs"]
mod normative_contract_support;
#[path = "source_binding_registry_normative_contract_tests.rs"]
mod normative_contract_tests;
#[path = "source_binding_registry_publication_route_tests.rs"]
mod publication_route_tests;
#[path = "source_binding_registry_sensitive_surface_tests.rs"]
mod sensitive_surface_tests;
