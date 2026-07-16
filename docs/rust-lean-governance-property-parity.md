# Rust-Lean Governance Property Parity

Rust exposes one flattened `GovernanceProperty` enum in `src/sacrifice.rs`.
Lean keeps the same audit surface split across protocol governance properties
and graph-audit/kernel checks. The table separates Lean-internal
characterization lemmas from the live Rust-to-Lean differential tests.

| Rust `GovernanceProperty` | Rust check surface | Lean target | Lean-internal characterization | Rust-Lean differential coverage |
| --- | --- | --- | --- | --- |
| `Consistency` | `check_graph_consistency` | `Protocol.GovernanceProperty.Consistency`; `AuditCheck.consistency`; `GraphConsistency` / `auditCheckConsistencyCore` | `rustCheckGraphConsistency_iff_canonical`; `auditCheckStatus_passed_implies_consistencyCore`; rule-level checker contract `lean_full_consistency_executable_iff_axiom` pins the canonical consistency axiom. | `tests/parity_edge_cases.rs`: edge cases plus rich pass chain and `rich_consistency_peer_relative_reject`. |
| `Solidarity` | `check_graph_solidarity` | `Protocol.GovernanceProperty.Solidarity`; `AuditCheck.solidarity`; `GraphSolidarity` / `auditCheckSolidarityCore` | `rustCheckGraphSolidarity_iff_canonical`; `auditCheckStatus_passed_implies_solidarityCore`; `auditCheckHolds` maps `.solidarity` to `GraphSolidarity`. | `tests/parity_edge_cases.rs`: edge cases plus rich pass chain and `rich_solidarity_split_threshold_reject`. |
| `Monotonicity` | `check_graph_monotonicity` | `Protocol.GovernanceProperty.Monotonicity`; `AuditCheck.monotonicity`; `GraphMonotonicity` / `auditCheckMonotonicityCorePolarityAware` | `rustCheckGraphMonotonicity_iff_canonical`; `auditCheckStatus_passed_implies_monotonicityCorePolarityAware`; theorem-backed rows cite per-harness `...RejectsMonotonicity` theorems. | `tests/parity_edge_cases.rs`: edge cases plus rich pass chain and `rich_monotonicity_deny_threshold_reject`. |
| `Strategyproofness` | `check_graph_strategyproofness` | `Protocol.GovernanceProperty.Strategyproofness`; `AuditCheck.strategyproofness`; `GraphStrategyproofness` / `auditCheckStrategyproofnessCore` | `rustCheckGraphStrategyproofness_iff_canonical`; `auditCheckStatus_passed_implies_strategyproofnessCore`; `auditCheckHolds` maps `.strategyproofness` to `GraphStrategyproofness`; the Rust audit surface uses the additive perturbation checker. | `tests/parity_edge_cases.rs`: edge cases, rich all-check corpus, and the dedicated additive corpus including `threshold_manipulable`, `threshold_already_permitted`, `peer_relative`, and deterministic multi-node cases. |
| `Certifiability` | `check_graph_certifiability` | `AuditCheck.certifiability`; `canonicalGraphCertifiableProjection` | `auditCertifiability_passed_iff_acyclic_and_canonical`. | `tests/parity_edge_cases.rs`: edge cases plus rich pass chain and `rich_cyclic_triangle_nonpass` skip parity. |
| `ObservableDeterminacy` | `check_graph_observable_determinacy` | `AuditCheck.observableDeterminacy`; `auditTraversalDeterministic` | `auditObservableDeterminacy_passed_iff_canonical_traversal_unique`; skip behavior pinned by `rust_check_observable_determinacy_skipped_on_empty`, `rust_check_observable_determinacy_skipped_on_node_limit`, and `rust_check_observable_determinacy_skipped_on_order_limit`. | `tests/parity_edge_cases.rs`: edge cases plus rich pass chain, `rich_observable_over_node_limit_nonpass`, and `rich_cyclic_triangle_nonpass`. |
| `Corrigibility` | `check_graph_corrigibility` | `AuditCheck.corrigibility`; `canonicalGraphCorrigibleProjection` | `auditCorrigibility_passed_iff_acyclic_and_canonical`. | `tests/parity_edge_cases.rs`: edge cases plus rich pass chain and `rich_cyclic_triangle_nonpass` skip parity. |
| `CompositionalSafety` | `check_graph_compositional_safety` | `AuditCheck.compositionalSafety`; `canonicalGraphCompositionalSafetyProjection` | `auditCompositionalSafety_passed_iff_acyclic_nonempty_and_canonical`; empty-graph skip behavior pinned by `rust_check_graph_compositional_safety_skipped_on_empty`. | `tests/parity_edge_cases.rs`: edge cases plus rich pass chain and `rich_cyclic_triangle_nonpass` skip parity. |
| `NonVacuous` | `check_graph_nonvacuity` | `Protocol.GovernanceProperty.NonVacuous`; `AuditCheck.nonvacuous`; `canonicalGraphNonVacuousProjection` | `auditNonVacuity_passed_iff_canonical_nonvacuous`. | `tests/parity_edge_cases.rs`: edge cases plus rich pass chain and `rich_nonvacuous_all_deny_reject`. |

The apparent "Lean 5, Rust 9" mismatch is therefore not an unproved enum
divergence. Rust flattens five protocol governance properties plus four
additional graph-audit/kernel checks into one operational sacrifice vocabulary;
Lean keeps those layers separate and connects the executable graph checks
through the contracts, characterization lemmas, and differential tests named
above.
