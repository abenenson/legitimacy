# Lean Module Architecture

This is the canonical subsystem ledger for repository reviews. Read it before
reviewing theorem claims, extractor evidence, or audit-lane documentation. It
records the maintained Lean subsystem map, the major Rust module map, and the
coexisting graph carriers that are easy to confuse.

Counts below were computed from the current tree with `find ... -name '*.lean'`
and `find ... -name '*.rs'`; LOC means physical source lines.

## Lean Subsystem Ledger

| Name | Purpose | LOC | File-count | Key theorem/type names | Authority-class |
| --- | --- | ---: | ---: | --- | --- |
| `Attacks` | Formal sidecar attack families for decomposition and sovereignty inversion: what local or layered failures look like before they are bridged to kernel obligations. | 271 | 2 | `Decomposition`, `SovereigntyInversion`, `csm_no_permitting_decomposition`, `strat_immune_to_inversion` | supporting |
| `Audits` | Manual theorem-facing audit case studies outside the main leaderboard lanes, including Sleeper Agents and AI Control extraction characterizations. | 1516 | 3 | `sleeperAgentExtractedGovernanceGraph`, `sleeper_agent_canonical_governance_verdict`, `AdmitsDeceptiveDeployment`, `aiControlTrustedMonitoringGovernanceGraph` | standalone-sidecar |
| `Behavioral` | Behavioral lineage models that connect constitutional-AI and AI-control style subjects to governance games, spectral embeddings, and substrate verdicts. | 5206 | 10 | `ConstitutionalAIBehavioralLineage`, `constitutionalAI_zero_consistency_vulnerability_implies_game_strategyproof`, `constitutionalAIWitness5_cv_pos`, `BehavioralGovernanceGame` | supporting |
| `Bridges` | Cross-literature and cross-layer bridges: graph-to-spectral correspondences, ELK/deception/AI-control interfaces, and conditional compiled-claim monitor retagging. | 3703 | 11 | `GraphSpectralCorrespondence`, `graph_strategyproof_iff_zero_consistency_vulnerability`, `AIControlProtocol`, `compiledClaimAttack_monitorRetag_ofMonitorEvidence` | supporting |
| `CaseStudies` | Concrete worked repairs and harness endpoints, especially Codex threshold repair and universal-repair boundaries over audit graphs. | 2315 | 3 | `codexHarnessSpectralGraph`, `codexHarness_stage4_threshold_removed_derives_finite_audit`, `general_adjudicated_repair_removes_spectral_vulnerability`, `no_universal_repair_preserves_strict_decision_preservation` | supporting |
| `Detection` | Completeness and incompleteness facts for finite-profile diagnostic detectors, including explicit counterexamples to profile-bounded detection. | 1000 | 1 | `DetectionSoundOn`, `DetectionCompleteOn`, `enumerativeDetector_sound_complete_on_canonicalPeerRelativeGraphs`, `no_finite_profile_detector_complete_on_SingleNodeGraphs` | standalone-sidecar |
| `Diagnostics` | Predicate layer for decision systems and graph diagnostics, including the typeclass/pipeline bridge used by the impossibility spine. | 690 | 5 | `GraphConsistencyP`, `GraphSolidarityP`, `GraphMonotonicityP`, `graphConsistency_eq_graphConsistencyP` | supporting |
| `Extract` | Lean-side extraction contracts, canonical inputs, AST witness binding, and Lean audit-wrapper characterization lemmas for Rust-parity projections. | 4137 | 25 | `BoundedExtractorContract`, `bounded_extractor_contract_sound`, `ASTTheoremWitnessBinding`, `auditNonVacuity_passed_iff_canonical_nonvacuous` | faithfulness |
| `Fixtures` | Executable Lean roots that export spectral and ASI parity fixture bytes for Rust parity checks. | 246 | 2 | `payload`, `safetySpecReductionExampleArtifactJson`, `main` | tooling |
| `Foundations` | Core modeled objects: claims, binary decisions, `GovernanceGraph`, weighted graph carriers, supervised systems, and structural peer-relativity. | 2055 | 5 | `GovernanceGraph`, `graphDecide`, `GraphN`, `NontrivialSymmetricScarcePeerRelativeBinaryAllocator` | headline |
| `Impossibility` | The diagnostic obstruction cluster: axiom lattice/independence, peer-relative class facts, and the reachable-stage headline theorem. | 3343 | 10 | `reachable_peer_relative_decisive_stage_obstructs_diagnostics`, `peerGraph_not_consistent`, `complete_first_effective_implies_reachable_peer_relative_decisive`, `nonPeerRelative_escapes_impossibility` | headline |
| `Kernel` | Semantic legitimacy kernel data and obligations, including runtime kernel classes, observability, corrigibility, compositional safety, and DAG bridges. | 4973 | 12 | `IsLegitimacyKernel`, `IsSemanticLegitimacyKernel`, `KernelSemanticBridge`, `dagPeerRelativeSurfaceMap_impossibility` | headline |
| `Kernelization` | Authority-surface honesty layer for source-to-kernelization claims, structural examples, semantic failure certificates, and tightness witnesses. | 1613 | 6 | `KernelizationExtractorContract`, `kernelization_honesty`, `SemanticBridgeFailureWitness`, `KernelizationHonesty_operationally_distinguishes_clean_and_certified` | faithfulness |
| `MultiAgentComposition` | Cross-agent composition substrate, compatibility witnesses, failure certificates, and two-agent fixtures. | 1533 | 3 | `KernelGovernedAgent`, `MultiAgentSystem`, `CrossAgentSacrificeCertificate`, `anchored_representative_kernel_realized_iff_all_compatible` | supporting |
| `MultiAgentJointCapabilityComposition` | Joint-capability composition substrate and Spera-style fixture families for canonical, Boolean, and independence cases. | 1615 | 4 | `JointCapability`, `JointCapabilityCompatibility`, `joint_capability_forbidden_excluded`, `multi_agent_kernel_joint_capability_composition_safe` | supporting |
| `Probes` | Proof-campaign scaffolds for governance institutions, adjunctions, and RG-flow structure that are built but not headline theorem surfaces. | 1994 | 2 | `GovernanceInstitution`, `GovernanceAdjunction`, `concrete_iterated_RG_n5`, `ASISpectralSignature` | tooling |
| `Protocol` | Formal protocol state, compilation witnesses, graph-native claim-step policy and fixtures, drift/corrigibility transitions, risk reports, and multi-principal corrigibility bridges. | 4706 | 13 | `CompiledGovernance`, `CompiledGovernance.ClaimDecomposition`, `peerGraphCompiledPolicyThreeClaimAttack`, `corrigibility_under_recompile` | supporting |
| `Reflective` | Modal and reflective audit substrate, production self-audit, critical-capability reflection, and no-bridge orthogonality results. | 3602 | 12 | `production_self_audit_boxed_by_loeb`, `ProductionSelfAuditCertificateHolds`, `no_universal_audit_passes_to_graph_diagnostics_bridge`, `no_graph_identification_free_reachable_obstruction_certificate_bridge` | orthogonality |
| `Results` | Public theorem facade and finite audit lanes: semantic bridge, capability scaling, admissibility audits, leaderboard witnesses, and ASI packages. | 13527 | 38 | `Decision3.ofBinary`, `semanticKernel_iff_runtime_diagnostic_spectral_layers`, `capability_scaling_shared_cliff`, `governanceAdmissibilityVerdict` | headline |
| `Safety` | Kernel-safety trajectory and activation-gate layer: no undeclared sacrifice, reachable-state safety, schedule safety, and safety envelopes. | 6432 | 16 | `noUndeclaredSacrifice`, `kernelReachabilitySafety`, `stateful_agent_schedule_safety`, `KernelGovernedTrajectory` | headline |
| `Spectral` | Spectral graph substrate, capacity thresholds, channel bridges, cross-scale universality, dynamics, ASI embeddings, and certificate packages. | 14647 | 50 | `GovGraph`, `C_star_exists`, `channel_capacity_bounds_C_star`, `stackelberg_convergence_limit_iff_zero_consistency_vulnerability` | headline |

## Rust Module Ledger

| Name | Purpose | LOC | File-count | Key theorem/type names | Authority-class |
| --- | --- | ---: | ---: | --- | --- |
| `src` root files | Crate API and domain model: claimants, claims, estates, allocations, rules, compiled verdicts, certificates, sacrifices, monitoring, and public re-exports. | 5429 | 15 | `Claim`, `RuleSpec`, `CompiledRule`, `DeclaredSacrifice` | supporting |
| `src/axioms` | Executable runtime-kernel and graph-diagnostic checks used by compile and audit surfaces. | 4624 | 18 | `KernelAxiom`, `check_graph_consistency`, `check_graph_monotonicity`, `check_graph_nonvacuity` | headline |
| `src/behavioral` | Rust mirror of the Constitutional AI lineage witness and substrate verdict helpers. | 465 | 2 | `ConstitutionalAIBehavioralLineage`, `ConstitutionalAISubstrateVerdict`, `constitutional_ai_witness_lineage5`, `substrate_verdict` | supporting |
| `src/bin` | Command-line executable entry points for the audit agent and observed-runtime import tool. | 853 | 2 | `legitimacy-audit-agent`, `import_codex_observed_runtime`, `main` | tooling |
| `src/extract` | Source-to-graph extractor, AST theorem-witness hashing, audit reports, review overlays, corpus packs, and lane-specific parsers. | 11303 | 22 | `extract_governance_artifacts`, `GovernanceExtractionReport`, `AstTheoremWitness`, `audit_governance_graph` | faithfulness |
| `src/graph` | Runtime governance graph data model, validation, traversal, edge transforms, and cycle checking. | 2121 | 6 | `GovernanceGraph`, `GovernanceNode`, `traverse`, `detect_cycles` | supporting |
| `src/ledger` | SQLite-backed append-only audit ledger and chain verification for compiled rules, certificates, sacrifices, and paradox results. | 1275 | 3 | `Ledger`, `LedgerAuditReport`, `ChainVerificationResult`, `TableChainStatus` | tooling |
| `src/paradox` | Operational finite-search paradox diagnostics for allocation rules and governance graphs; intentionally outside the canonical axiom inventory. | 652 | 1 | `ParadoxType`, `run_paradox_suite`, `GraphParadoxType`, `compositional_alabama` | standalone-sidecar |
| `src/policy` | TOML policy and graph parsers, including Claude-directory metadata parsing. | 1301 | 4 | `PolicySpec`, `GraphPolicySpec`, `load_policy_file`, `load_graph_file` | tooling |
| `src/protocol` | Runtime protocol state machine for declaration, compilation, measurement, activation, drift reporting, supervision, and recompilation. | 2104 | 5 | `ProtocolState`, `declare`, `activate`, `report_drift` | supporting |
| `src/rules` | Built-in allocation and harness rules used by examples and tests. | 151 | 1 | `proportional_rule`, `jefferson_rule`, `webster_rule`, `claude_agent_sdk_hooks_rule` | tooling |
| `src/spectral` | Executable spectral diagnostics, concrete graph fixtures, C* calculations, coarse-graining, noisy-channel calibration, and positive-procedure helpers. | 3379 | 11 | `capacity`, `cv`, `c_star`, `governance_certificate` | supporting |

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
