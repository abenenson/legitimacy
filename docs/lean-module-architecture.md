# Lean Module Architecture

This is the canonical subsystem ledger for repository reviews. Read it before
reviewing theorem claims, extractor evidence, or audit-lane documentation. It
records the maintained Lean subsystem map, the major Rust module map, and the
coexisting graph carriers that are easy to confuse.

The [formal overview](formal-overview.md) explains the results and their relationships;
the [claim ledger](claim-ledger.md) records evidence status. This document maps
those results to source modules. The [paper index](../papers/README.md) provides
section-level routes through all six manuscripts.

Inventory snapshot: 2026-09-15, source tree at `5e1c1a9`. Counts cover tracked
first-party `.lean` files under `lean/Legitimacy` and `.rs` files under `src`,
including tests embedded there. LOC means physical source lines. Root files
are counted separately from recursive directory rows; build outputs and the
separate `tests/` directory are excluded.

## Lean Subsystem Ledger

| Name | Purpose | LOC | File-count | Key theorem/type names | Authority-class |
| --- | --- | ---: | ---: | --- | --- |
| [`lean/Legitimacy root files`](../lean/Legitimacy) | Top-level composition and lifecycle interfaces, safety-spec reduction, verification trilemma, regex core and subsystem import roots. | 3085 | 10 | `MultiAgentEdgeLocalComposition.lean`, `SafetySpecReduction.lean`, `SelfModificationLifecycle.lean`, `VerificationTrilemma.lean` | supporting |
| [`Attacks`](../lean/Legitimacy/Attacks) | Formal sidecar attack families for decomposition and sovereignty inversion: what local or layered failures look like before they are bridged to kernel obligations. | 271 | 2 | `Decomposition`, `SovereigntyInversion`, `csm_no_permitting_decomposition`, `strat_immune_to_inversion` | supporting |
| [`Audits`](../lean/Legitimacy/Audits) | Manual theorem-facing audit case studies outside the main leaderboard lanes, including Sleeper Agents and AI Control extraction characterizations. | 1517 | 3 | `sleeperAgentExtractedGovernanceGraph`, `sleeper_agent_canonical_governance_verdict`, `AdmitsDeceptiveDeployment`, `aiControlTrustedMonitoringGovernanceGraph` | standalone-sidecar |
| [`Behavioral`](../lean/Legitimacy/Behavioral) | Behavioral lineage models that connect constitutional-AI and AI-control style subjects to governance games, spectral embeddings, and substrate verdicts. | 6207 | 12 | `ConstitutionalAIBehavioralLineage`, `constitutionalAI_zero_consistency_vulnerability_implies_game_strategyproof`, `constitutionalAIWitness5_cv_pos`, `BehavioralGovernanceGame` | supporting |
| [`Bridges`](../lean/Legitimacy/Bridges) | Cross-literature and cross-layer bridges: graph-to-spectral correspondences, ELK/deception/AI-control interfaces, and conditional compiled-claim monitor retagging. | 3703 | 11 | `GraphSpectralCorrespondence`, `graph_strategyproof_iff_zero_consistency_vulnerability`, `AIControlProtocol`, `compiledClaimAttack_monitorRetag_ofMonitorEvidence` | supporting |
| [`CaseStudies`](../lean/Legitimacy/CaseStudies) | Concrete worked repairs and harness endpoints, especially Codex threshold repair and universal-repair boundaries over audit graphs. | 2839 | 5 | `codexHarnessSpectralGraph`, `codexHarness_stage4_threshold_removed_derives_finite_audit`, `general_adjudicated_repair_removes_spectral_vulnerability`, `no_universal_repair_preserves_strict_decision_preservation` | supporting |
| [`Detection`](../lean/Legitimacy/Detection) | Completeness and incompleteness facts for finite-profile diagnostic detectors, including explicit counterexamples to profile-bounded detection. | 1000 | 1 | `DetectionSoundOn`, `DetectionCompleteOn`, `enumerativeDetector_sound_complete_on_canonicalPeerRelativeGraphs`, `no_finite_profile_detector_complete_on_SingleNodeGraphs` | standalone-sidecar |
| [`Diagnostics`](../lean/Legitimacy/Diagnostics) | Predicate layer for decision systems and graph diagnostics, including the typeclass/pipeline bridge used by the impossibility spine. | 690 | 5 | `GraphConsistencyP`, `GraphSolidarityP`, `GraphMonotonicityP`, `graphConsistency_eq_graphConsistencyP` | supporting |
| [`Extract`](../lean/Legitimacy/Extract) | Lean extraction contracts and restricted modeled-language decision preservation, AST witness binding, and audit-wrapper parity lemmas; separate from production Rust parsing. | 7552 | 32 | `BoundedExtractorContract`, `extractRustHookCore_decision_equivalent`, `ASTTheoremWitnessBinding`, `auditNonVacuity_passed_iff_canonical_nonvacuous` | faithfulness |
| [`Fixtures`](../lean/Legitimacy/Fixtures) | Executable Lean roots that export spectral and ASI parity fixture bytes for Rust parity checks. | 424 | 5 | `payload`, `safetySpecReductionExampleArtifactJson`, `main` | tooling |
| [`Foundations`](../lean/Legitimacy/Foundations) | Core modeled objects: claims, binary decisions, `GovernanceGraph`, weighted graph carriers, supervised systems, and structural peer-relativity. | 2528 | 6 | `GovernanceGraph`, `graphDecide`, `GraphN`, `NontrivialSymmetricScarcePeerRelativeBinaryAllocator` | headline |
| [`Impossibility`](../lean/Legitimacy/Impossibility) | Diagnostic obstruction classes, median-inclusive scarcity theorem, necessity and separating witnesses, and the narrower reachable-stage result. | 4808 | 12 | `symmetric_scarce_coupled_allocators_obstructed`, `maxStrengthNode_separates_structural_from_symmetricScarceCoupled`, `reachable_peer_relative_decisive_stage_obstructs_diagnostics` | headline |
| [`Kernel`](../lean/Legitimacy/Kernel) | Semantic legitimacy kernel data and obligations, including runtime kernel classes, observability, corrigibility, compositional safety, and DAG bridges. | 4978 | 12 | `IsLegitimacyKernel`, `IsSemanticLegitimacyKernel`, `KernelSemanticBridge`, `dagPeerRelativeSurfaceMap_impossibility` | headline |
| [`Kernelization`](../lean/Legitimacy/Kernelization) | Authority-surface honesty layer for source-to-kernelization claims, structural examples, semantic failure certificates, and tightness witnesses. | 1613 | 6 | `KernelizationExtractorContract`, `kernelization_honesty`, `SemanticBridgeFailureWitness`, `KernelizationHonesty_operationally_distinguishes_clean_and_certified` | faithfulness |
| [`MultiAgentComposition`](../lean/Legitimacy/MultiAgentComposition) | Cross-agent composition substrate, compatibility witnesses, failure certificates, and two-agent fixtures. | 1533 | 3 | `KernelGovernedAgent`, `MultiAgentSystem`, `CrossAgentSacrificeCertificate`, `anchored_representative_kernel_realized_iff_all_compatible` | supporting |
| [`MultiAgentJointCapabilityComposition`](../lean/Legitimacy/MultiAgentJointCapabilityComposition) | Joint-capability composition substrate and Spera-style fixture families for canonical, Boolean, and independence cases. | 1839 | 4 | `JointCapability`, `JointCapabilityCompatibility`, `joint_capability_forbidden_excluded`, `multi_agent_kernel_joint_capability_composition_safe` | supporting |
| [`Probes`](../lean/Legitimacy/Probes) | Proof-campaign scaffolds for governance institutions, adjunctions, and RG-flow structure that are built but not headline theorem surfaces. | 1994 | 2 | `GovernanceInstitution`, `GovernanceAdjunction`, `concrete_iterated_RG_n5`, `ASISpectralSignature` | tooling |
| [`Protocol`](../lean/Legitimacy/Protocol) | Compilation and policy witnesses, drift/recompilation, multi-principal supervisory preservation, and the finite executed-composition model and repair. | 5623 | 16 | `CompiledGovernance`, `corrigibility_under_recompile`, `ExecutedComposition.delivery_log_refines`, `ExecutedComposition.repair_safe` | supporting |
| [`Reflective`](../lean/Legitimacy/Reflective) | Modal and reflective audit substrate, production self-audit, critical-capability reflection, and no-bridge orthogonality results. | 3692 | 12 | `production_self_audit_boxed_by_loeb`, `ProductionSelfAuditCertificateHolds`, `no_universal_audit_passes_to_graph_diagnostics_bridge`, `no_graph_identification_free_reachable_obstruction_certificate_bridge` | orthogonality |
| [`Results`](../lean/Legitimacy/Results) | Public theorem facade and finite audit lanes: semantic bridge, capability scaling, admissibility audits, leaderboard witnesses, and ASI packages. | 13527 | 38 | `Decision3.ofBinary`, `semanticKernel_iff_runtime_diagnostic_spectral_layers`, `capability_scaling_shared_cliff`, `governanceAdmissibilityVerdict` | headline |
| [`Safety`](../lean/Legitimacy/Safety) | Kernel-safety trajectory and activation-gate layer: no undeclared sacrifice, reachable-state safety, schedule safety, and safety envelopes. | 6628 | 16 | `noUndeclaredSacrifice`, `kernelReachabilitySafety`, `stateful_agent_schedule_safety`, `KernelGovernedTrajectory` | headline |
| [`Spectral`](../lean/Legitimacy/Spectral) | Spectral graph substrate, capacity thresholds, channel bridges, cross-scale universality, dynamics, ASI embeddings, and certificate packages. | 15697 | 52 | `GovGraph`, `C_star_exists`, `channel_capacity_bounds_C_star`, `stackelberg_convergence_limit_iff_zero_consistency_vulnerability` | headline |
| [`Verified`](../lean/Legitimacy/Verified) | Named theorems for the Lean literal-string parser and matcher subset; not a correctness proof for the production Rust parser. | 101 | 1 | `Regex.parse_UserPromptSubmit_eq`, `Regex.parse_literal_event_name_isSome` | supporting |

## Rust Module Ledger

| Name | Purpose | LOC | File-count | Key theorem/type names | Authority-class |
| --- | --- | ---: | ---: | --- | --- |
| [`src`](../src) root files | Crate API and domain model: claimants, claims, estates, allocations, rules, compiled verdicts, certificates, sacrifices, monitoring, and public re-exports. | 5540 | 15 | `Claim`, `RuleSpec`, `CompiledRule`, `DeclaredSacrifice` | supporting |
| [`src/axioms`](../src/axioms) | Executable runtime-kernel and graph-diagnostic checks used by compile and audit surfaces. | 4624 | 18 | `KernelAxiom`, `check_graph_consistency`, `check_graph_monotonicity`, `check_graph_nonvacuity` | headline |
| [`src/behavioral`](../src/behavioral) | Rust mirror of the Constitutional AI lineage witness and substrate verdict helpers. | 465 | 2 | `ConstitutionalAIBehavioralLineage`, `ConstitutionalAISubstrateVerdict`, `constitutional_ai_witness_lineage5`, `substrate_verdict` | supporting |
| [`src/bin`](../src/bin) | CLI entry points for graph audits, observed-runtime import, bounded Codex capture and the executed-composition experiment. | 1096 | 4 | `legitimacy-audit-agent`, `import_codex_observed_runtime`, `legitimacy-codex-capture-v0`, `legitimacy-executed-composition` | tooling |
| [`src/extract`](../src/extract) | Source-to-graph extractor, AST theorem-witness hashing, audit reports, review overlays, corpus packs, and lane-specific parsers. | 11625 | 23 | `extract_governance_artifacts`, `GovernanceExtractionReport`, `AstTheoremWitness`, `audit_governance_graph` | faithfulness |
| [`src/graph`](../src/graph) | Runtime governance graph data model, validation, traversal, edge transforms, and cycle checking. | 2132 | 6 | `GovernanceGraph`, `GovernanceNode`, `traverse`, `detect_cycles` | supporting |
| [`src/ledger`](../src/ledger) | SQLite-backed append-only audit ledger and chain verification for compiled rules, certificates, sacrifices, and paradox results. | 1275 | 3 | `Ledger`, `LedgerAuditReport`, `ChainVerificationResult`, `TableChainStatus` | tooling |
| [`src/paradox`](../src/paradox) | Operational finite-search paradox diagnostics for allocation rules and governance graphs; intentionally outside the canonical axiom inventory. | 652 | 1 | `ParadoxType`, `run_paradox_suite`, `GraphParadoxType`, `compositional_alabama` | standalone-sidecar |
| [`src/policy`](../src/policy) | TOML policy and graph parsers, including Claude-directory metadata parsing. | 1301 | 4 | `PolicySpec`, `GraphPolicySpec`, `load_policy_file`, `load_graph_file` | tooling |
| [`src/protocol`](../src/protocol) | Runtime protocol state machine for declaration, compilation, measurement, activation, drift reporting, supervision, and recompilation. | 2104 | 5 | `ProtocolState`, `declare`, `activate`, `report_drift` | supporting |
| [`src/rules`](../src/rules) | Built-in allocation and harness rules used by examples and tests. | 151 | 1 | `proportional_rule`, `jefferson_rule`, `webster_rule`, `claude_agent_sdk_hooks_rule` | tooling |
| [`src/spectral`](../src/spectral) | Executable spectral diagnostics, concrete graph fixtures, C* calculations, coarse-graining, noisy-channel calibration, and positive-procedure helpers. | 3407 | 11 | `capacity`, `cv`, `c_star`, `governance_certificate` | supporting |
| [`src/executed_composition`](../src/executed_composition) | Finite experiment host, independently reconstructed deliveries, checked Lean transition-table consumption and signed capture verification. | 603 | 2 | `Grant`, `Event`, `SignedRun`, `check_signed` | supporting |
| [`src/trajectory`](../src/trajectory) | Versioned trace validation, replay and authority receipts, replay-bound composition evaluation, and bounded Codex capture/import. | 15874 | 42 | `TrajectoryTraceV0`, `VerifiedTrajectoryReplayV0`, `evaluate_replay_bound_composition_v0`, `VerifiedReplayAuthorityReceiptV0` | supporting |

## Canonical Graph Carriers

Several graph encodings coexist. They are not interchangeable unless a theorem
or explicit extractor contract says so.

- `GovernanceGraph := List GovernanceNodeFn`
  (`lean/Legitimacy/Foundations/Graph.lean:57`) is the impossibility and
  diagnostic carrier. This is a headline carrier.
- `AuditGovernanceGraph`
  (`lean/Legitimacy/Results/GovernanceAdmissibilityAudit/Core.lean:96`) is the
  audit-engine and finite-fixture verdict carrier. It ports the Rust extracted
  graph surface, including nodes, edges, gates, traversal, and audit checks;
  some fixtures reject specific diagnostics, while others pass.
- The `(1)` to typeclass diagnostic bridge
  `graphConsistency_eq_graphConsistencyP`
  (`lean/Legitimacy/Diagnostics/DecisionSystem.lean`) is proven. It connects
  the function-list `GovernanceGraph` diagnostic with the `DecisionSystem`
  predicate formulation for graph consistency.
- The `(1)` to `(2)` carrier bridge is not proven. The only current lifts named
  `liftGovernanceGraphToAuditGraph` in the PythonHookCore and RustHookCore
  verdict-pullback modules are lossy: they materialize placeholder audit nodes
  and do not identify the full audit carrier with the impossibility carrier.
  This boundary is documented by negative theorems in
  `lean/Legitimacy/Reflective/PeerRelativeAuditOrthogonality.lean:77-175`,
  including
  `no_universal_audit_passes_to_graph_diagnostics_bridge` and
  `no_graph_identification_free_reachable_obstruction_certificate_bridge`.
- Other siloed encodings are present and should be treated by their own local
  contracts: `GovernanceGraph3` in `lean/Legitimacy/Results/Composition.lean`,
  `ExtractedGovernanceGraph` in `lean/Legitimacy/VerificationTrilemma.lean`,
  and `GovGraph ℚ n` in the spectral subsystem.

## Review Rule

When a review cites a theorem, first identify the subsystem row and graph
carrier. If the claim crosses `GovernanceGraph`, `AuditGovernanceGraph`, or
`GovGraph ℚ n`, require a named bridge theorem or classify the statement as a
boundary/open item.
