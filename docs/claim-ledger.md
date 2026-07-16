# Claim Ledger

This is the canonical evidence map for public claims in the README and the six
papers. It does not add new theorem, Rust, or paper claims. It names where each
headline claim is load-bearing, where it is only executable evidence, and where
the current substrate is deliberately scoped.

Statuses:

- **Formally proved**: Lean proves the statement over the modeled artifact.
- **Empirically enforced**: Rust checks, fixtures, or tests enforce the artifact
  behavior, but Lean does not prove Rust execution or arbitrary parser fidelity.
- **Scoped**: the claim is true only under the named representation, model, or
  bridge assumptions.
- **Open**: the public text names a gap or frontier surface.
- **Future-work**: the repository intentionally does not yet provide evidence.

When a Lean name is too long for one line, the namespace and declaration are
split. The full name is their dot-join.

## Kernel And Boundary

### C01. The artifact is a semantic legitimacy kernel, not a scalar score.

Status: **Formally proved** for the modeled semantic-kernel target; **scoped**
for public claims about source-derived systems.

Public source: README thesis paragraph; paper 02, "Abstract" and "3. The Kernel
Target"; paper 03, "1.1 Kernel thesis".

Lean evidence:

- `Legitimacy.semanticKernel_iff_runtime_diagnostic_spectral_layers`
  `lean/Legitimacy/Results/SemanticBridge.lean:74`
- `Legitimacy.semanticKernel_iff_runtime_diagnostic_spectral_layers_unfolded`
  `lean/Legitimacy/Results/SemanticBridge.lean:32`

Rust evidence:

- `src::extract::audit::audit_governance_graph`
  `src/extract/audit.rs:147`
- `src::extract::audit::run_graph_axiom_checks`
  `src/extract/audit.rs:282`

Reviewer note: the theorem decomposes the strengthened target. It does not say
that runtime obligations alone imply graph diagnostics or spectral structure.

### C02. Runtime obligations, graph diagnostics, and spectral witness are
explicit layers.

Status: **Formally proved** as a decomposition; **scoped** away from raw source
semantics.

Public source: README "Theorem Spine"; paper 02, "3. The Kernel Target"; paper
03, "4. Semantic Kernel Bridge".

Lean evidence:

- `Legitimacy.semanticKernel_implies_runtime_diagnostics_and_spectral`
  `lean/Legitimacy/Results/SemanticBridge.lean:93`
- `Legitimacy.runtime_kernel_does_not_imply_graph_diagnostics`
  `lean/Legitimacy/Results/SemanticBridge.lean:225`
- `Legitimacy.runtime_kernel_and_diagnostics_does_not_imply_spectralWellConnected`
  `lean/Legitimacy/Results/SemanticBridge.lean:336`

Rust evidence:

- `src::axioms::kernel::KernelAxiom`
  `src/axioms/kernel/mod.rs:29`
- `src::extract::audit::run_graph_axiom_checks`
  `src/extract/audit.rs:282`
- `src::extract::spectral::spectral_analysis`
  `src/extract/spectral.rs:118`

Reviewer note: the bridge is load-bearing. A clean runtime interface is not a
proof of diagnostic or spectral legitimacy.

### C03. The bounded extractor contract is the formal source-to-kernel boundary.

Status: **Formally proved** for contracted extractors; **empirically enforced**
for the current Rust extractor and fixtures.

Public source: README "Boundaries And Gates"; paper 02, "6. Evidence That the
Object Is Buildable"; paper 03, "6.1 Bounded extractor contract and Rust
parity"; paper 01, "Current Evidence Lanes".

Lean evidence:

- `Legitimacy.BoundedExtractorContract`
  `lean/Legitimacy/Extract/Soundness.lean:105`
- `Legitimacy.bounded_extractor_contract_sound`
  `lean/Legitimacy/Extract/Soundness.lean:121`
- `Legitimacy.extractor_byte_stable_soundness_boundary`
  `lean/Legitimacy/Extract/Soundness.lean:173`
- `Legitimacy.canonical_leaderboard_fixtures_byte_parity_certificate`
  `lean/Legitimacy/Extract/Soundness.lean:340`

Rust evidence:

- `src::extract::extract_governance_artifacts_with_review`
  `src/extract/mod.rs:460`
- Namespace: `tests::autogen_parity`
  Function:
  `leaderboard_extracted_graphs_are_byte_identical_across_runs_and_match_canonical_snapshots`
  `tests/autogen_parity.rs:466`
- `tests::extract::extract_output_is_byte_stable_for_multi_violation_fixture`
  `tests/extract.rs:251`

Reviewer note: Lean proves the contract shape. It does not verify arbitrary
tree-sitter parsing or Rust execution.

### C04. Evidence tiers are part of the public claim surface.

Status: **Empirically enforced** and **scoped**.

Public source: paper 01, "The setup", "Current Evidence Lanes", and "Why the
Evidence Tiers Matter"; README "Boundaries And Gates"; `docs/boundary.md`.

Lean evidence:

- `Legitimacy.EmpiricalParityCertificate`
  `lean/Legitimacy/Extract/Soundness.lean:229`
- `Legitimacy.EmpiricalByteParityCertificate`
  `lean/Legitimacy/Extract/Soundness.lean:325`

Rust evidence:

- `src::extract::review::ExtractionEvidenceTier`
  `src/extract/review.rs:5`
- `src::extract::ClaimCorpusProvenance`
  `src/extract/mod.rs:267`
- `src::extract::audit::normalize_claims_for_graph`
  `src/extract/audit.rs:234`

Reviewer note: heuristic rows are not theorem-backed source-level findings.
Broad upstream claims require reviewed or theorem-backed promotion.

## Impossibility And Sacrifice

### C05. Reachable scarce peer-relative decisive stages force a diagnostic
tradeoff.

Status: **Formally proved**.

Public source: README "Theorem Spine"; paper 02, "4. The Forcing Theorem";
paper 03, "2. Three-Diagnostic Obstruction Theorem".

Lean evidence:

- `Legitimacy.reachable_peer_relative_decisive_stage_obstructs_diagnostics`
  `lean/Legitimacy/Impossibility/PeerRelativeReachable.lean:103`
- `Legitimacy.nontrivial_symmetric_scarce_peer_relative_binary_allocators_obstructed`
  `lean/Legitimacy/Foundations/StructuralPeerRelative.lean:272`
- `Legitimacy.complete_first_effective_obstructs_diagnostics_via_reachable`
  `lean/Legitimacy/Impossibility/PeerRelativeReachable.lean:149`

Rust evidence:

- `src::axioms::diagnostics::graph::consistency::check_graph_consistency`
  `src/axioms/diagnostics/graph/consistency.rs:6`
- `src::axioms::diagnostics::graph::solidarity::check_graph_solidarity`
  `src/axioms/diagnostics/graph/solidarity.rs:12`
- `src::axioms::diagnostics::graph::monotonicity::check_graph_monotonicity`
  `src/axioms/diagnostics/graph/monotonicity.rs:233`

Reviewer note: the theorem needs reachability, transparent-prefix, structural
scarcity, symmetry, and non-denying suffix hypotheses. It is not the claim that
any graph containing any peer-relative component is impossible.

### C06. The theorem boundary is honest: some weakened peer-relative slogans
are false.

Status: **Formally proved** countermodel boundary.

Public source: paper 03, "3.5 Non-peer-relative escape trichotomy" and "3.6
Lean-side correspondence for headline claims"; paper 02, "4. The Forcing
Theorem".

Lean evidence:

- `Legitimacy.peer_relative_by_context_alone_insufficient`
  `lean/Legitimacy/Foundations/StructuralPeerRelative.lean:298`
- `Legitimacy.peer_relative_with_finite_estate_without_symmetry_insufficient`
  `lean/Legitimacy/Foundations/StructuralPeerRelative.lean:418`
- `Legitimacy.upstream_deny_all_gate_vacuous_countermodel`
  `lean/Legitimacy/Foundations/StructuralPeerRelative.lean:431`
- `Legitimacy.reachable_stage_qualifiers_individually_necessary`
  `lean/Legitimacy/Impossibility/PeerRelativeReachable.lean:309`

Rust evidence: none beyond the diagnostic checkers in C05.

Reviewer note: these are anti-overclaim anchors. They should be cited whenever
the theorem is summarized informally.

### C07. Strategyproofness is a derived bridge, not the minimal obstruction.

Status: **Formally proved**.

Public source: paper 02, "4. The Forcing Theorem"; paper 03, "2.2
Strategyproofness as a derived bridge"; paper 06, "7. Three-axis
Triangulation".

Lean evidence:

- `Legitimacy.solidarity_monotonicity_imply_strategyproof`
  `lean/Legitimacy/Impossibility/AxiomIndependence.lean:349`
- `Legitimacy.not_exists_non_strategyproof_consistent_solid_monotone`
  `lean/Legitimacy/Impossibility/AxiomIndependence.lean:791`

Rust evidence:

- `src::axioms::diagnostics::graph::strategyproofness::check_graph_strategyproofness`
  `src/axioms/diagnostics/graph/strategyproofness.rs:9`

Reviewer note: the three-diagnostic obstruction is consistency, solidarity, and
monotonicity. Strategyproofness is the paper-facing fourth consequence.

### C08. Non-peer-relative escape exists but has structural costs.

Status: **Formally proved** for the modeled escape lemmas; **scoped** for the
pipeline/kernel trichotomy.

Public source: paper 03, "3.5 Non-peer-relative escape trichotomy"; paper 06,
"2. Prior Art and Adjacent Programs".

Lean evidence:

- `Legitimacy.nonPeerRelative_escapes_impossibility`
  `lean/Legitimacy/Results/NonPeerRelative.lean:385`
- `Legitimacy.nonPeerRelative_is_threshold`
  `lean/Legitimacy/Results/NonPeerRelative.lean:393`
- `Legitimacy.nonPeerRelative_monotone_strategyproof_claimantConstant`
  `lean/Legitimacy/Results/NonPeerRelative.lean:413`
- `Legitimacy.nonPeerRelative_cannot_allocate_finite_estate`
  `lean/Legitimacy/Results/NonPeerRelative.lean:423`
- `Legitimacy.non_peer_relative_collapse_or_infeasible_or_exits_kernel`
  `lean/Legitimacy/Impossibility/PeerRelativeClass/Escape.lean:122`

Rust evidence:

- `src::spectral::non_peer_relative::is_non_peer_relative`
  `src/spectral/non_peer_relative.rs:3`
- `src::spectral::non_peer_relative::is_threshold_structured`
  `src/spectral/non_peer_relative.rs:7`

Reviewer note: non-peer-relative graphs can evade the obstruction at graph
level, but the public claim is not that they recover substantive allocation.

### C09. Live activation is blocked unless forced sacrifices are declared.

Status: **Formally proved** for the modeled live-compiled surface;
**empirically enforced** by protocol and sacrifice compilation tests.

Public source: README "Boundaries And Gates"; paper 02, "4.1 Twin Safety-Stack
Headlines"; paper 03, "3.7 The impossibility-safety canonical pair".

Lean evidence:

- `Legitimacy.Safety.noUndeclaredSacrifice`
  `lean/Legitimacy/Safety/KernelSafety/BinaryDecisionPipeline.lean:132`
- ``
- `Legitimacy.Safety.binaryDecisionPipeline_noUndeclaredSacrifice`
  `lean/Legitimacy/Safety/KernelSafety/BinaryDecisionPipeline.lean:160`

Rust evidence:

- `src::protocol::transitions::compile`
  `src/protocol/transitions.rs:91`
- `src::sacrifice::compile_graph_with_sacrifices`
  `src/sacrifice.rs:311`
- `tests::protocol::protocol_compile_rejects_peer_relative_surface_without_forced_sacrifices`
  `tests/protocol.rs:167`
- `tests::sacrifice::graph_sacrifice_certificate_rejects_skipped_kernel_evidence`
  `tests/sacrifice.rs:329`

Reviewer note: Rust protocol activation rejects undeclared violations; the Lean
theorem is over the modeled complete peer-relative surface.

### C10. Kernel-governed trajectories do not silently degrade.

Status: **Formally proved** for covered trajectories and schedules.

Public source: README "Theorem Spine"; paper 02, "4.1 Twin Safety-Stack
Headlines"; paper 03, "3.7 The impossibility-safety canonical pair".

Lean evidence:

- `Legitimacy.Safety.kernelReachabilitySafety`
  `lean/Legitimacy/Safety/KernelSafety/ReachabilityStack.lean:125`
- `Legitimacy.Safety.stateful_agent_schedule_safety`
  `lean/Legitimacy/Safety/KernelSafety/StatefulScheduleSafety.lean:179`
- `Legitimacy.Safety.kernelGovernedTrajectory_from_forcedConsistencySacrifice`
  `lean/Legitimacy/Safety/KernelSafety/ReachabilityStack.lean:667`

Rust evidence:

- `src::protocol::transitions::activate`
  `src/protocol/transitions.rs:236`
- `src::protocol::transitions::check_decision`
  `src/protocol/transitions.rs:295`
- `src::protocol::state::non_sacrificed_monitoring_properties`
  `src/protocol/state.rs:377`
- `tests::protocol::live_monitoring_covers_non_sacrificed_properties`
  `tests/protocol.rs:267`

Reviewer note: this is not a universal alignment theorem. It assumes the
trajectory or schedule is covered by governance-or-certificate hypotheses.

### C11. Universal repair is possible only at a weaker faithfulness bar.

Status: **Formally proved**.

Public source: `docs/repository-context.md`, "Supporting Theorems"; paper 03,
"6.5 A formal negative result for bounded corrigibility".

Lean evidence:

- `Legitimacy.no_universal_repair_preserves_strict_decision_preservation`
  `lean/Legitimacy/CaseStudies/UniversalRepair.lean:976`
- `Legitimacy.nonCollapsedReplacementRepair_universal_under_nontrivial_faithfulness`
  `lean/Legitimacy/CaseStudies/UniversalRepair.lean:990`

Rust evidence: none. This is a Lean-only repair-boundary claim.

Reviewer note: the positive result repairs at non-collapsed faithfulness, not
strict preservation of every original decision.

## Executable Audit And Harness Claims

### C12. The canonical audit surface has nine named checks.

Status: **Formally modeled** in Lean and **empirically enforced** in Rust.

Public source: README "Broader CLI Surface"; paper 03, "6.3 Empirical audit"; paper
05, "3.1 The 9-element audit".

Lean evidence:

- `Legitimacy.governanceAdmissibilityVerdict`
  `lean/Legitimacy/Results/GovernanceAdmissibilityAudit/Checks.lean:685`
- `Legitimacy.auditCheckStatus`
  `lean/Legitimacy/Results/GovernanceAdmissibilityAudit/Checks.lean:385`
- `Legitimacy.auditCheckStatus_pass_reflects_auditSemantics`
  `lean/Legitimacy/Results/GovernanceAdmissibilityAudit/Checks.lean:548`
- `Legitimacy.cyclicSkippedAuditGraph_undischarged`
  `lean/Legitimacy/Results/GovernanceAdmissibilityAudit/Fixtures.lean:136`

Rust evidence:

- `src::extract::audit::run_graph_axiom_checks`
  `src/extract/audit.rs:282`
- `src::axioms::kernel::KernelAxiom::graph_axiom_name`
  `src/axioms/kernel/mod.rs:49`
- `scripts::canonical_axiom_inventory`
  `scripts/canonical-axiom-inventory.sh:3`

Reviewer note: skipped evidence is absent evidence, not a pass. Cyclic skipped
graphs cannot promote to theorem-facing legitimacy.

### C13. The Codex hook graph rejection is theorem-backed over the finite graph.

Status: **Formally proved** over the extracted finite graph; **empirically
enforced** for fixture extraction and audits; **scoped** away from all live
Codex behavior.

Public source: README "Worked extractions: the obstruction on real-agent graphs"; paper 01, "Exploratory
Findings"; paper 03, "1.4 Contributions"; paper 05, "6. Codex Harness Worked
Example".

Lean evidence:

- `Legitimacy.codexHooksGovernanceAdmissibilityRejectsMonotonicity`
  `lean/Legitimacy/Results/CodexAdmissibilityAudit.lean:209`
- `Legitimacy.codexHooks_preToolUseRegistration_hookRegistrationEscalateThresholdGate`
  `lean/Legitimacy/Results/CodexAdmissibilityAudit.lean:236`
- `Legitimacy.codexHarness_stage1_detects_monotonicity_failure`
  `lean/Legitimacy/CaseStudies/CodexHarness.lean:58`

Rust evidence:

- `src::extract::rust_hook_core_parser::parse_rust_hook_core`
  `src/extract/rust_hook_core_parser.rs:110`
- Namespace: `tests::codex_mechanical`
  Function:
  `mechanical_codex_source_graph_distinguishes_schema_polarity_from_legacy_delta`
  `tests/codex_mechanical.rs:62`
- `tests::autogen_parity::shared_canonical_inputs_include_codex_hooks_fixture`
  `tests/autogen_parity.rs:427`

Reviewer note: the compositional-Alabama probe is Rust-only diagnostic evidence,
not a Lean axiom.

Rust-only probe evidence:

- `src::paradox::graph::compositional_alabama`
  `src/paradox/graph.rs:43`
- `src::extract::audit::run_graph_paradox_suite`
  `src/extract/audit.rs:357`

### C14. The Claude Agent SDK hook graph rejection and review-required result are
finite-graph claims.

Status: **Formally proved** over the extracted finite graph; **scoped** to the
modeled graph and lattice choice.

Public source: README "Worked extractions: the obstruction on real-agent graphs"; paper 03,
"1.4 Contributions"; `docs/repository-context.md`, "Review-Required Axiom
Revision".

Lean evidence:

- `Legitimacy.claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicity`
  `lean/Legitimacy/Results/ClaudeAgentSDKAdmissibilityAudit.lean:188`
- `Legitimacy.claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired`
  `lean/Legitimacy/Results/ClaudeAgentSDKAdmissibilityAudit.lean:201`
- `Legitimacy.codex_claude_sdk_review_required_joint_rejection`
  `lean/Legitimacy/Results/ClaudeAgentSDKAdmissibilityAudit.lean:218`

Rust evidence:

- `src::extract::python_hook_core_parser::parse_python_hook_core`
  `src/extract/python_hook_core_parser.rs:112`
- `tests::claude_agent_sdk::claude_agent_sdk_hooks_policy_exposes_monotonicity_failure`
  `tests/claude_agent_sdk.rs:53`
- `tests::autogen_parity::shared_canonical_inputs_include_claude_agent_sdk_hooks_fixture`
  `tests/autogen_parity.rs:445`

Reviewer note: the review-required result is an alternate lattice verdict. It
does not erase the canonical production-lattice rejection.

### C15. AI Control fixture passes are represented-slice, polarity-aware claims.

Status: **Formally proved** for committed fixture graphs; **scoped** to hand
representation and polarity metadata.

Public source: paper 05, "2. AI Control Case Study and Verdict"; paper 06, "2.
Prior Art and Adjacent Programs" and "6.3 Composition with the AI Control
structural audit".

Lean evidence:

- `Legitimacy.aiControl_protocol_upfrontAuditing_polarity_aware_governance_verdict`
  `lean/Legitimacy/Audits/AIControl.lean:652`
- `Legitimacy.aiControl_protocol_trustedMonitoring_polarity_aware_governance_verdict`
  `lean/Legitimacy/Audits/AIControl.lean:660`
- `Legitimacy.aiControl_protocol_trustedMonitoringDefer_polarity_aware_governance_verdict`
  `lean/Legitimacy/Audits/AIControl.lean:668`
- `Legitimacy.aiControl_protocol_untrustedMonitoring_polarity_aware_governance_verdict`
  `lean/Legitimacy/Audits/AIControl.lean:676`
- `Legitimacy.aiControl_protocol_trustedEditing_polarity_aware_governance_verdict`
  `lean/Legitimacy/Audits/AIControl.lean:684`
- `Legitimacy.ai_control_fixture_graphs_receive_legitimate_verdict`
  `lean/Legitimacy/Bridges/KorbakAIControlBridge.lean:51`
- `Legitimacy.defer_to_resample_has_no_current_extracted_graph`
  `lean/Legitimacy/Bridges/KorbakAIControlBridge.lean:104`

Rust evidence: none for the hand-modeled Lean fixtures. Rust audit semantics
are represented by the same nine-check surface in C12.

Reviewer note: this is not a proof of the empirical AI Control safety case and
does not cover defer-to-resample.

### C16. The sleeper-agent result is a represented-slice monotonicity theorem,
not a classifier.

Status: **Formally proved** for the fixed represented subject and check; **scoped**
away from empirical model internals.

Public source: paper 05, "3. Sleeper-agent Monotonicity Test"; paper 06, "2.
Prior Art and Adjacent Programs".

Lean evidence:

- `Legitimacy.deceptive_deployment_on_not_audit_monotone`
  `lean/Legitimacy/Audits/SleeperCharacterization.lean:131`
- `Legitimacy.admitsDeceptiveDeploymentOnCheck_iff_AdmitsDeceptiveDeploymentOn`
  `lean/Legitimacy/Audits/SleeperCharacterization.lean:300`
- `Legitimacy.sleeperAgentAdmitsDeceptiveDeployment`
  `lean/Legitimacy/Audits/SleeperCharacterization.lean:356`
- `Legitimacy.admitsDeceptiveDeployment_strict_refinement_of_monotonicity_failure`
  `lean/Legitimacy/Audits/SleeperCharacterization.lean:568`
- `Legitimacy.hubinger_deception_subsumed_by_kernel_substrate`
  `lean/Legitimacy/Bridges/HubingerDeceptionBridge.lean:60`

Rust evidence: none. This is a Lean audit-subject characterization.

Reviewer note: monotonicity failure is necessary for the formal sleeper split
under the legacy predicate, but not sufficient. The paper explicitly rejects the
classifier reading.

### C17. The Constitutional AI bridge is a narrow lineage realization.

Status: **Formally proved** for the constructed audit subject; **scoped** away
from full Anthropic Constitutional AI.

Public source: paper 05, "4. Constitutional AI Lineage"; paper 06, "2. Prior
Art and Adjacent Programs".

Lean evidence:

- `Legitimacy.ConstitutionalAITrainedAuditSubject_of_respects_resolution`
  `lean/Legitimacy/Behavioral/ConstitutionalAILineage.lean:187`
- `Legitimacy.ConstitutionalAIBehavioralLineage.spectralBehavioralEmbedding`
  `lean/Legitimacy/Behavioral/ConstitutionalAILineage.lean:708`
- Namespace: `Legitimacy.ConstitutionalAIBehavioralLineage`
  Declaration:
  `constitutionalAI_zero_consistency_vulnerability_implies_game_strategyproof`
  `lean/Legitimacy/Behavioral/ConstitutionalAILineage.lean:803`
- Namespace: `Legitimacy.ConstitutionalAIBehavioralLineage`
  Declaration: `constitutionalAIWitness_substrate_verdict`
  `lean/Legitimacy/Behavioral/ConstitutionalAIWitnesses.lean:318`

Rust evidence: none.

Reviewer note: this bridges a constructed CAI-shaped rule layer to the spectral
behavioral game. It is not a behavioral embedding of Anthropic's full CAI
training process.

### C18. Decomposition attacks hit a block-or-sacrifice disjunction.

Status: **Formally proved** for the modeled decomposition bridge.

Public source: paper 05, "5. Decomposition Attack Bridge"; paper 03, "1.4
Contributions".

Lean evidence:

- `Legitimacy.decomposition_attack_blocked_or_sacrificed`
  `lean/Legitimacy/Bridges/DecompositionAttackKernelBridge.lean:291`
- `Legitimacy.sleeperAgentDecompositionAttackClass`
  `lean/Legitimacy/Bridges/DecompositionAttackKernelBridge.lean:377`
- `Legitimacy.sacrifice_leg_witness`
  `lean/Legitimacy/Bridges/DecompositionAttackKernelBridge.lean:474`
- `Legitimacy.block_leg_witness`
  `lean/Legitimacy/Bridges/DecompositionAttackKernelBridge.lean:501`

Rust evidence: none.

Reviewer note: the theorem is about the modeled kernel step and certificate
surface. It is not a universal taxonomy of all decomposition attacks.

### C19. The Codex harness repair case study derives its repaired verdict.

Status: **Formally proved** for the repaired typed graph; **scoped** away from a
claim that the live vendor protocol already contains the repair.

Public source: paper 05, "6. Codex Harness Worked Example"; paper 03, "1.4
Contributions".

Lean evidence:

- `Legitimacy.codexHarnessDerived_stage2_threshold`
  `lean/Legitimacy/CaseStudies/CodexHarness.lean:219`
- `Legitimacy.codexHarness_repaired_spectral_zero_derives_monotonicity_pass`
  `lean/Legitimacy/CaseStudies/CodexHarness.lean:561`
- `Legitimacy.codexHarness_repaired_spectral_zero_derives_nonvacuity_pass`
  `lean/Legitimacy/CaseStudies/CodexHarness.lean:601`
- `Legitimacy.codexHarness_stage4_threshold_removed_derives_finite_audit`
  `lean/Legitimacy/CaseStudies/CodexHarness.lean:680`

Rust evidence:

- `tests::codex_mechanical::mechanically_extract_codex_graph`
  `tests/codex_mechanical.rs:116`

Reviewer note: the original extracted graph remains rejected; the repaired
verdict is a typed case-study endpoint.

## Scaling, Capacity, And ASI Scope

### C20. Positive spectral vulnerability creates a critical capability threshold.

Status: **Formally proved** in the spectral surrogate; **empirically mirrored**
by Rust spectral checks.

Public source: README "Theorem Spine"; paper 03, "5.6 Critical capability and
the Stackelberg limit"; paper 04, "3.1 The governance graph and its spectral
vulnerability".

Lean evidence:

- `Legitimacy.C_star`
  `lean/Legitimacy/Spectral/Capacity/CriticalCapability.lean:40`
- `Legitimacy.C_star_exists`
  `lean/Legitimacy/Spectral/Capacity/CriticalCapability.lean:55`
- `Legitimacy.phase_transition_at_C_star`
  `lean/Legitimacy/Spectral/Capacity/CriticalCapability.lean:231`

Rust evidence:

- `src::spectral::critical::c_star`
  `src/spectral/critical.rs:25`
- `src::spectral::critical::sp_violation`
  `src/spectral/critical.rs:14`
- `tests::spectral_well_connected::cli_paper_diagnostics_marks_c_star_undefined_when_cv_is_zero`
  `tests/spectral_well_connected.rs:266`

Reviewer note: capability enters the spectral surrogate. This is not a theorem
about behavioral learning dynamics.

### C21. Unbounded spectral stability is equivalent to zero consistency vulnerability.

Status: **Formally proved** in the spectral surrogate.

Public source: README "Theorem Spine"; paper 04, "3. Stackelberg Asymptotic
Limit"; paper 03, "5.6 Critical capability and the Stackelberg limit".

Lean evidence:

- `Legitimacy.stackelberg_convergence_limit_iff_zero_consistency_vulnerability`
  `lean/Legitimacy/Spectral/Dynamics/StackelbergConvergence.lean:188`
- `Legitimacy.eventually_no_stable_equilibrium_of_positive_cv`
  `lean/Legitimacy/Spectral/Dynamics/StackelbergConvergence.lean:133`
- `Legitimacy.zeroConsistencyVulnerability_has_arbitrarily_large_stable_equilibria`
  `lean/Legitimacy/Spectral/Dynamics/StackelbergConvergence.lean:167`

Rust evidence:

- `src::spectral::critical::sp_violation`
  `src/spectral/critical.rs:14`
- `src::spectral::tests::critical_capability_matches_reciprocal_cv_on_uniform_triangle`
  `src/spectral/critical.rs:120`

Reviewer note: this characterizes the formal spectral equilibrium predicate, not
arbitrary strategic behavior by deployed models.

### C22. Verification capacity transmits to the same `C*` threshold.

Status: **Formally proved** for the stated deterministic and calibrated-channel
models; **scoped** away from general Shannon equality.

Public source: README "Theorem Spine"; paper 04, "2. Capacity Converse"; paper
06, "6. Two C* Notions".

Lean evidence:

- `Legitimacy.GovernanceChannel.channel_capacity_bounds_C_star`
  `lean/Legitimacy/Spectral/Channels/CStarChannelBridge.lean:551`
- `Legitimacy.GovGraph.governance_capacity_alignment_threshold`
  `lean/Legitimacy/Spectral/Capacity/CapacityConverse.lean:244`
- `Legitimacy.GovGraph.binary_output_log_rate_converse`
  `lean/Legitimacy/Spectral/Capacity/CapacityConverse.lean:95`
- `Legitimacy.GovernanceChannel.fixed_noisyThreshold_capacity_not_concrete_C_star_bridge`
  `lean/Legitimacy/Spectral/Channels/CStarChannelBridge.lean:601`

Rust evidence:

- `src::spectral::mod::capacity`
  `src/spectral/mod.rs:34`
- `src::spectral::mod::capacity_bound`
  `src/spectral/mod.rs:39`
- `tests::parity_concrete_values::concrete_bifurcation_n5`
  `tests/parity_concrete_values.rs:106`

Reviewer note: the positive capacity and converse statements live on explicit
channel constructions. The paper explicitly rejects a fixed-channel Shannon
capacity equals concrete `C*` overclaim.

### C23. RG and cross-scale claims are finite-family or hypothesis-bounded.

Status: **Formally proved** for named finite families and hypotheses; **open**
for substrate-wide universality.

Public source: paper 03, "5.7 RG flow and scale-local basin structure"; paper
04, "7. RG Flow and Family Universality"; `docs/safety-and-asi-scope.md`.

Lean evidence:

- `Legitimacy.concrete_iterated_RG_n5`
  `lean/Legitimacy/Spectral/CrossScale/RGFlow/N5.lean:25`
- `Legitimacy.concrete_iterated_RG_n5_parametric_signature`
  `lean/Legitimacy/Spectral/CrossScale/RGFlow/N5.lean:123`
- `Legitimacy.finite_crossScale_certified_spectral_universality`
  `lean/Legitimacy/Spectral/CrossScale/FiniteCrossScaleUniversality/Universality.lean:383`
- `Legitimacy.discharged_archetypes_admissible_window_actual_gaps`
  `lean/Legitimacy/Spectral/CrossScale/FiniteCrossScaleUniversality/Universality.lean:338`

Rust evidence:

- `src::spectral::coarse_grain::coarse_grain`
  `src/spectral/coarse_grain.rs:8`
- `src::spectral::coarse_grain::preserves_solidarity`
  `src/spectral/coarse_grain.rs:47`
- `src::spectral::coarse_grain::breaks_monotonicity`
  `src/spectral/coarse_grain.rs:177`
- `tests::parity_concrete_values::concrete_iterated_rg_n5_parametric_signature`
  `tests/parity_concrete_values.rs:165`

Reviewer note: exact n=5 results should not be read as an all-sizes fixed-point
theorem.

### C24. ASI/safety bridges are spectral and structural, not universal
alignment proofs.

Status: **Formally proved** for family-aligned complete carriers; **open** for a
substrate-wide free bridge.

Public source: README "Theorem Spine"; paper 03, "Abstract" and "5.7 RG flow";
paper 06, "4. GS-AI Verifier Positioning"; `docs/safety-and-asi-scope.md`.

Lean evidence:

- `Legitimacy.ASIBridge.uniKFamily_spectralWellConnected`
  `lean/Legitimacy/Spectral/ASIBridge/Native.lean:501`
- `Legitimacy.ASIBridge.asiCompleteGraph_spectralGap_eq`
  `lean/Legitimacy/Spectral/ASIBridge/Native.lean:252`
- `Legitimacy.ASIBridge.uniK_n_asiSpectralSignature_depth3`
  `lean/Legitimacy/Spectral/ASIBridge/FamilyAlignment.lean:232`
- `Legitimacy.ASIBridge.asiSpectralSignature_uniK_n_iff_positive_depth3_cv`
  `lean/Legitimacy/Spectral/ASIBridge/FamilyAlignment.lean:241`
- Namespace: `Legitimacy.ASIBridge`
  Declaration:
  `uniK_n_family_aligned_native_asi_signature_kernelInvariant`
  `lean/Legitimacy/Spectral/ASIBridge/FamilyAlignment.lean:536`
- `Legitimacy.ASIBridge.uniK7_family_aligned_native_asi_signature_kernelInvariant`
  `lean/Legitimacy/Spectral/ASIBridge/FamilyAlignment.lean:743`
- `Legitimacy.ASIBridge.uniK9_family_aligned_native_asi_signature_kernelInvariant`
  `lean/Legitimacy/Spectral/ASIBridge/FamilyAlignment.lean:945`

Rust evidence:

- `tests::asi_parity::safety_spec_reduction_fixtures_round_trip`
  `tests/asi_parity.rs:29`
- `scripts::check_asi_parity_manifest`
  `scripts/check-asi-parity-manifest.sh:5`

Reviewer note: current `ASIBridge` names are historical Lean namespaces. The
proved content is scoped kernel invariance for named spectral carriers. Two of
the spectral facts are genuinely general in the carrier size, not finite-table:
`uniKFamily_spectralWellConnected` discharges `SpectralWellConnected` for every
`n` with `2 ≤ n`, and `asiCompleteGraph_spectralGap_eq` gives the closed-form
spectral gap `n + 1` for every complete carrier of size `n + 1`. The "family
universality" and ASI-signature work that remains size-indexed (uniK7, uniK9)
and the staged native ASI signature are scoped to their named sizes; the
all-`n` spectral statements above are the load-bearing generality here.

### C25. Capacity-aware ELK and the two-`C*` paper are positioning bridges.

Status: **Formally proved** for the repository-defined structural correspondences;
**open** for full ELK or joint feedback-channel/governance-channel analysis.

Public source: paper 06, "2. Prior Art and Adjacent Programs" and "6. Two C*
Notions"; paper 04, "6. Shannon Negative Bridge".

Lean evidence:

- `Legitimacy.GovGraph.hidden_authority_certificate_rate_bounded`
  `lean/Legitimacy/Bridges/CapacityAwareELK.lean:140`
- `Legitimacy.Safety.christiano_elk_structural_correspondence`
  `lean/Legitimacy/Bridges/ChristianoELKStructuralBridge.lean:44`
- `Legitimacy.GovernanceChannel.channelCapacity_asNoisyThresholdChannel_eq_log_two_sub_binEntropy`
  `lean/Legitimacy/Spectral/Channels/NoisyThresholdClosedForm.lean:172`
- `Legitimacy.GovernanceChannel.fixed_noisyThreshold_capacity_not_concrete_C_star_bridge`
  `lean/Legitimacy/Spectral/Channels/CStarChannelBridge.lean:601`

Rust evidence: none beyond spectral parity in C22 and C24.

Reviewer note: the repository does not formalize external feedback-channel
`C*` results. It only maps the notational and structural relationship.

## Positioning And Scope

### C26. The legitimacy kernel is one static-snapshot GS-AI verifier target.

Status: **Formally proved** for the static-snapshot instance; **scoped** away
from dynamic environment safety and LawZero/Scientist-AI completeness.

Public source: paper 06, "4. GS-AI Verifier Positioning"; README "Boundary And
Gates".

Lean evidence:

- `Legitimacy.GSAIKernelizationVerifier.contractSurface_intro`
  `lean/Legitimacy/Bridges/GuaranteedSafeAIBridge.lean:156`
- `Legitimacy.gs_ai_fixture_certificates_cover_rejected_leaderboard_harnesses`
  `lean/Legitimacy/Bridges/GuaranteedSafeAIBridge.lean:325`
- `Legitimacy.legitimacy_substrate_is_static_gs_ai_snapshot_instance`
  `lean/Legitimacy/Bridges/GuaranteedSafeAIBridge.lean:362`
- `Legitimacy.Safety.safety_spec_reduces_to_kernel_audit`
  `lean/Legitimacy/SafetySpecReduction.lean:113`

Rust evidence:

- `src::safety_spec_reduction::KernelAuditConjunction::from_artifact_and_obligations`
  `src/safety_spec_reduction.rs:355`
- `tests::asi_parity::safety_spec_reduction_fixtures_round_trip`
  `tests/asi_parity.rs:29`

Reviewer note: this supplies one typed verifier-target filling. It does not
prove empirical safety for arbitrary deployments.

### C27. The verification-trilemma position is bounded-domain decision-definedness with entailed soundness and forced non-generality.

Status: **Formally proved** for the repository's trilemma model.

Public source: paper 06, "5. Verification Trilemma".

Lean evidence:

- `Legitimacy.legitimacy_audit_diagonal_positioning`
  `lean/Legitimacy/VerificationTrilemma.lean:201`
- `Legitimacy.compiler_audit_diagonal_positioning`
  `lean/Legitimacy/VerificationTrilemma.lean:305`
- `Legitimacy.trilemma_definedness_failure_witness`
  `lean/Legitimacy/VerificationTrilemma.lean:271`
- `Legitimacy.audit_decision_defined_implies_soundness`
  `lean/Legitimacy/VerificationTrilemma.lean:167`
- `Legitimacy.audit_defined_on_all_distributions_impossible`
  `lean/Legitimacy/VerificationTrilemma.lean:183`
- `Legitimacy.trilemma_decision_defined_independent`
  `lean/Legitimacy/VerificationTrilemma.lean:410`
- `Legitimacy.unrestricted_distribution_not_relevant`
  `lean/Legitimacy/VerificationTrilemma.lean:354`

Rust evidence: none. The theorem-backed claim is bounded-domain
decision-definedness on the typed finite substrate, with soundness entailed by
decision-definedness and unrestricted generality definitionally unavailable.
`native_decide`-style corpus execution is finite-substrate evidence, not a
polynomial-time tractability predicate or Rust complexity proof.

Reviewer note: this is not an escape from the trilemma. It states which
predicate is genuinely contingent in the current substrate. The decision-definedness
clause has a genuine independence witness; soundness is entailed by
`audit_decision_defined_implies_soundness`, and all-distribution definedness is
definitionally blocked by `audit_defined_on_all_distributions_impossible` inside
the current `LegitimacyAudit` type.

### C28. The program is a governance-rule axis, not a replacement for adjacent
alignment work.

Status: **Scoped** positioning claim with formal anchors underneath.

Public source: paper 06, "2. Prior Art and Adjacent Programs", "7. Three-axis
Triangulation", and "8. Conclusion"; paper 02, "7. What This Is Not".

Lean evidence:

- `Legitimacy.binaryDecisionPipeline_effectiveSurface_complete_three_axiom_obstruction`
  `lean/Legitimacy/Impossibility/PeerRelativeClass/Obstructions.lean:220`
- `Legitimacy.reachable_peer_relative_decisive_stage_obstructs_diagnostics`
  `lean/Legitimacy/Impossibility/PeerRelativeReachable.lean:103`
- `Legitimacy.bounded_extractor_contract_sound`
  `lean/Legitimacy/Extract/Soundness.lean:121`

Rust evidence:

- `src::extract::audit::audit_governance_graph`
  `src/extract/audit.rs:147`
- `src::protocol::transitions::compile`
  `src/protocol/transitions.rs:91`

Reviewer note: the adjacent literatures study different objects: preference
aggregation, feedback channels, behavioral safety cases, runtime enforcement,
or verifier architectures. This repository supplies the governance-rule
structural-audit axis.

### C29. Harness verdicts are diagnostic-specific fixture claims, not
frontier-framework refutations.

Status: **Scoped** framing claim with theorem-backed fixture rows.

Public source: README "Worked extractions: the obstruction on real-agent graphs"; paper 03, "6.3
Executable audit results"; paper 05, "2. AI Control Case Study and Verdict";
paper 06, "2. Prior Art and Adjacent Programs"; docs/repository-context.md,
"Claim Ledger" and "Review-Required Axiom Revision".

Lean evidence:

- `Legitimacy.codexHooksGovernanceAdmissibilityRejectsMonotonicity`
  `lean/Legitimacy/Results/CodexAdmissibilityAudit.lean`
- `Legitimacy.claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicity`
  `lean/Legitimacy/Results/ClaudeAgentSDKAdmissibilityAudit.lean`
- `Legitimacy.crewAIHooksGovernanceAdmissibilityRejectsMonotonicity`
  `lean/Legitimacy/Results/CrewAIAdmissibilityAudit.lean`
- `Legitimacy.openClawInfraNonvacuityCheckFails`
  `lean/Legitimacy/Results/OpenClawAdmissibilityAudit.lean`
- `Legitimacy.autoGen_extracted_graph_is_self_legitimate`
  `lean/Legitimacy/Results/AutoGenAdmissibilityAudit.lean`
- `Legitimacy.aiControl_protocol_upfrontAuditing_legitimate`
  `lean/Legitimacy/Audits/AIControl.lean`

Rust evidence:

- `scripts/check-fixture-provenance.sh`
- `audits/fixtures/sources/leaderboard/test-source-disclosures.txt`

Reviewer note: Codex and Claude Agent SDK are theorem-backed extracted-graph
monotonicity rejections. CrewAI is a disclosed test-source monotonicity
rejection. OpenClaw is a nonvacuity rejection, not a monotonicity rejection.
AutoGen is a singleton test-source provenance pass. The five represented
AI-Control fixtures are `legitimate` under the current schema-derived
polarity-aware audit. None of these rows is a theorem that a frontier safety
framework is refuted or that a live product is unsafe.

## Supporting Impossibility And Safety Results

### C30. Three-valued composition reintroduces the obstruction that binary
nodes individually avoid.

Status: **Formally proved** for the modeled three-valued node composition.

Public source: paper 03, "2. Three-Diagnostic Obstruction Theorem" (Definition
2.4 governance node and the Escalate decision) and "6.7.8" composition follow-on;
paper 05, "5. Decomposition Attack Bridge".

Lean evidence:

- `Legitimacy.three_valued_composition_inadmissibility`
  `lean/Legitimacy/Results/Composition.lean:519`
- `Legitimacy.three_valued_escalationPolicyWitness_composition_inadmissibility`
  `lean/Legitimacy/Results/Composition.lean:499`

Rust evidence:

- `src::axioms::diagnostics::graph::monotonicity::check_graph_monotonicity`
  `src/axioms/diagnostics/graph/monotonicity.rs:233`

Reviewer note: the headline result is parametric. Any first-stage node
satisfying the escalation witness surface becomes inadmissible once composed with
the peer-relative downstream gate, because Escalate adds a competitive channel
that does not exist in the binary decision model. The concrete instance uses a
`thresholdNode3` first stage; the parametric statement is the load-bearing one.
This is a statement about the modeled three-valued node algebra, not about
arbitrary multi-stage live policies.

### C31. The multi-principal surface carries an Arrow-template impossibility with
an explicit pairwise frontier.

Status: **Formally proved** for the modeled three-principal/three-property
quorum witness.

Public source: paper 06, "2. Prior Art and Adjacent Programs" and "7. Three-axis
Triangulation"; paper 03, "1. Introduction" (Arrow/Young lineage).

Lean evidence:

- `Legitimacy.majorityQuorumRule_fails_arrow_triple`
  `lean/Legitimacy/Results/MultiPrincipal.lean:695`
- `Legitimacy.multi_principal_pairwise_achievability_with_majorityQuorum_obstruction`
  `lean/Legitimacy/Results/MultiPrincipal.lean:713`

Rust evidence: none. This is a Lean social-choice-template result over the
modeled quorum rule.

Reviewer note: the impossibility is the concrete majority-quorum witness, which
is unanimous and non-dictatorial but fails independence on a 3-principal
counterexample. The frontier theorem is the honesty anchor: each pair
among unanimity, independence, and non-dictatorship is realized by an explicit
rule (dictatorship, majority quorum, constant), so the result is a tight
three-way frontier on this witness, not a claim that no rule satisfies any two.

### C32. The three graph-diagnostic axioms are independently omissible, and the
strategyproofness boundary is mapped.

Status: **Formally proved** for the modeled governance-graph witnesses.

Public source: paper 03, "3. Tightness and Escape Characterization" and "3.6
Lean-side correspondence for headline claims"; paper 04, "Axiom independence";
`docs/repository-context.md`, "Supporting Theorems".

Lean evidence:

- `Legitimacy.exists_non_consistent_solid_monotone_strategyproof`
  `lean/Legitimacy/Impossibility/AxiomIndependence.lean:749`
- `Legitimacy.exists_non_solidarity_consistent_monotone_strategyproof`
  `lean/Legitimacy/Impossibility/AxiomIndependence.lean:758`
- `Legitimacy.exists_non_monotonicity_consistent_solid_strategyproof`
  `lean/Legitimacy/Impossibility/AxiomIndependence.lean:767`
- `Legitimacy.exists_non_strategyproof_consistent_monotone`
  `lean/Legitimacy/Impossibility/AxiomIndependence.lean:775`
- `Legitimacy.exists_non_strategyproof_consistent_solid`
  `lean/Legitimacy/Impossibility/AxiomIndependence.lean:782`
- `Legitimacy.not_exists_non_strategyproof_consistent_solid_monotone`
  `lean/Legitimacy/Impossibility/AxiomIndependence.lean:791`

Rust evidence:

- `src::axioms::diagnostics::graph::strategyproofness::check_graph_strategyproofness`
  `src/axioms/diagnostics/graph/strategyproofness.rs:9`

Reviewer note: each of consistency, solidarity, and monotonicity has a concrete
graph witness satisfying the other two diagnostics (and strategyproofness) while
failing the named one, so the three-axiom obstruction in C05 is tight rather than
redundant. The strategyproofness boundary is mapped, not asserted as a fourth
independent axiom: strategyproofness is independently omissible from
consistency-plus-monotonicity and from consistency-plus-solidarity, but the
fourth witness does not exist — solidarity together with monotonicity already
forces strategyproofness (the negative result), which is exactly the C07 derived
bridge read from the independence side.

### C33. Reachable-state and stateful-schedule safety prove no silent
degradation under the coverage hypothesis.

Status: **Formally proved** for covered trajectories and schedules.

Public source: paper 02, "4.1 Twin Safety-Stack Headlines"; paper 03, "3.7 The
impossibility-safety canonical pair".

Lean evidence:

- `Legitimacy.Safety.kernelReachabilitySafety`
  `lean/Legitimacy/Safety/KernelSafety/ReachabilityStack.lean:125`
- `Legitimacy.Safety.stateful_agent_schedule_safety`
  `lean/Legitimacy/Safety/KernelSafety/StatefulScheduleSafety.lean:179`

Rust evidence:

- `src::protocol::state::non_sacrificed_monitoring_properties`
  `src/protocol/state.rs:377`
- `tests::protocol::live_monitoring_covers_non_sacrificed_properties`
  `tests/protocol.rs:267`

Reviewer note: these are the two safety theorems underneath C10, named here as a
standalone stack. Every state reachable under a covered stateful schedule from an
invariant initial state is either still invariant or exposes a monitored sacrifice
certificate for a transition before the queried horizon. The coverage hypothesis
is the load-bearing scope: each realized action before the horizon must be
classified as kernel-governed or certificate-emitting. This is not a universal
alignment theorem and does not cover schedules outside the coverage hypothesis.

### C34. On the five-graph verification lattice, the corrigibility bridge
discharges exactly for the well-connected basin.

Status: **Formally proved** as a finite-lattice biconditional over the named
n = 5 verification lattice.

Public source: paper 03, "5.7 RG flow and scale-local basin structure"; paper
06, "4. GS-AI Verifier Positioning"; `docs/safety-and-asi-scope.md`.

Lean evidence:

- `Legitimacy.n5_bridge_discharges_iff_well_connected_basin`
  `lean/Legitimacy/Results/BasinIsASIClassification.lean:440`
- `Legitimacy.n5_bridge_discharges_iff_well_connected_basin_parametric`
  `lean/Legitimacy/Results/BasinIsASIClassification.lean:334`

Rust evidence: none. This is a Lean classification over the hand-named n = 5
lattice representatives and the spectral basin predicate.

Reviewer note: the biconditional is scoped to the explicit five-graph lattice
(`uniK5`, `asymK5`, `nearPath5`, `wheel5`, `bottleneck5`), proved by case split
on those representatives. The parametric form quantifies over every positive
tolerance, and the headline specializes it at one tolerance. This is a
finite-lattice iff result, not an all-`n` basin-classification theorem; the four
well-connected graphs discharge the bridge and the topologically asymmetric
`bottleneck5` representative refutes it.

### C35. Self-modification escape requires a concrete override-removal step, and
governed policy lifecycles do not silently degrade.

Status: **Formally proved** for the modeled action space and policy-transition
trajectory.

Public source: paper 03, "3.7 The impossibility-safety canonical pair"; paper
02, "4.1 Twin Safety-Stack Headlines"; `docs/safety-and-asi-scope.md`.

Lean evidence:

- `Legitimacy.selfmod_escape_requires_indexed_override_removal_step`
  `lean/Legitimacy/Results/SelfModBoundary.lean:72`
- `Legitimacy.policy_lifecycle_no_silent_degradation`
  `lean/Legitimacy/SelfModificationLifecycle.lean:391`

Rust evidence: none. These are Lean self-modification boundary and lifecycle
results.

Reviewer note: both statements are general over the action space, not finite
tables. The boundary theorem says any finite action sequence from an initial
override graph that ever permits a claim must contain an indexed step that
destroys the override, witnessing the exact prefix and removing action; it is a
structural decomposition, not a claim that escape is impossible. The lifecycle
theorem says every transition in a governed trajectory either preserves the
kernel or surfaces an indexed sacrifice with a changed effective-authority
surface, so degradation is never silent. The reflective and staged
self-modification work beyond this disjunction is not surfaced here.

### C36. The Claude Code public-governance hook graph rejection is theorem-backed
over the doc-derived fixture.

Status: **Formally proved** over the public-doc-derived governance graph;
**scoped** to that represented surface, not live Claude Code behavior. The graph
is derived from the public Claude Code hook/settings/command governance schema,
not extracted from closed-source handler implementations.

Public source: README "Why a frontier lab should care" and README
"Worked extractions: the obstruction on real-agent graphs"; paper 03 audit taxonomy (the proprietary Claude
Code product, treated as metadata-only).

Lean evidence:

- `Legitimacy.claudeCodeHooksGovernanceAdmissibilityRejectsMonotonicity`
  `lean/Legitimacy/Results/ClaudeCodeAdmissibilityAudit.lean:284`
- `Legitimacy.claudeCodeHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired`
  `lean/Legitimacy/Results/ClaudeCodeAdmissibilityAudit.lean:293`

Rust evidence: none beyond the public-schema fixture under
`examples/claude-code-fixture/`. The graph is doc-derived governance metadata
(31 nodes / 14 edges), distinct from the source-extracted Codex (C13) and Claude
Agent SDK (C14) lanes.

Reviewer note: the rejection is the same monotonicity diagnostic as C13/C14, and
it survives the polarity-aware review-required lattice (the review-required
companion theorem). The lane is honestly weaker than the source-extracted ones:
its graph encodes the documented public governance surface, so the result is a
claim about that represented schema, not a proved property of the closed-source
product.
