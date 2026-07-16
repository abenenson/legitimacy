/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.MultiAgentComposition
import Legitimacy.KernelizationAdversarialExtractor
import Legitimacy.Results.ClaudeAgentSDKAdmissibilityAudit
import Legitimacy.Results.CodexAdmissibilityAudit
import Legitimacy.Results.CrewAIAdmissibilityAudit
import Legitimacy.Results.OpenClawAdmissibilityAudit

/-!
# Guaranteed Safe AI bridge

This module gives a narrow, substrate-grounded bridge to Dalrymple, Skalse,
Bengio, Russell, Tegmark, Seshia, Omohundro, Szegedy, Goldhaber, Ammann,
Abate, Halpern, Barrett, Zhao, Tan, Wing, and Tenenbaum, "Towards Guaranteed
Safe AI: A Framework for Ensuring Robust and Reliable AI Systems"
(arXiv:2405.06624, 2024).

The instantiation is intentionally scoped to the static structural-governance
subset formalized here. A GS-AI world model is represented by a finite
`MultiAgentSystem` together with per-agent `KernelGovernedTrajectory`
witnesses; the safety specification is per-agent `IsSemanticLegitimacyKernel`;
and the verifier certificate carries both concrete governance-audit evidence
and the kernelization extractor contract surface used by the verifier target.
This is not Bengio et al.'s later Scientist-AI paper
(arXiv:2502.15657), and it is not a claim to model arbitrary deployment
environment dynamics.
-/

set_option autoImplicit false

namespace Legitimacy

/-! ## Static GS-AI component surface -/

/-- Dalrymple GS AI's three-component framework, stated at the level needed by
the local substrate: a world-model type, a safety specification over worlds,
and a verifier/certificate type for worlds satisfying the specification. -/
structure GuaranteedSafeAIInstance where
  /-- World model: the formal model of the system being safety-checked.
      `Type 1` rather than `Type` so the field can carry types whose own
      inhabitants are types — e.g., `MultiAgentSystem`, whose components
      carry kernel-data structures that themselves live in `Type`. This
      avoids universe-polymorphism gymnastics at every call site while
      remaining Mathlib-grade explicit. -/
  worldModel : Type 1
  /-- Safety specification: acceptable worlds. -/
  safetySpec : worldModel → Prop
  /-- Verifier: an auditable certificate for the safety specification.
      `Type 2` lets the verifier carry proof-producing structures whose
      fields quantify over the `Type 1` world-model substrate. -/
  verifier : (world : worldModel) → safetySpec world → Type 2

/-- Static structural-governance world model used by this bridge. The
`MultiAgentSystem` supplies the finite governance snapshot, and the trajectory
field records that each declared agent has an explicit kernel-governed
trajectory anchor. This is the local static-snapshot subset of GS AI's broader
world-model component. -/
structure StaticGovernanceWorldModel where
  system : MultiAgentSystem
  trajectories :
    ∀ agent, agent ∈ system.agents →
      Nonempty
        (Σ finalKernel : LegitimacyKernelData agent.sys,
          Safety.KernelGovernedTrajectory agent.sys agent.kernel finalKernel)

/-- Safety specification for the legitimacy instantiation: every declared
agent in the static multi-agent world carries a semantic legitimacy kernel. -/
def SemanticLegitimacySafetySpec
    (world : StaticGovernanceWorldModel) : Prop :=
  ∀ agent, agent ∈ world.system.agents →
    IsSemanticLegitimacyKernel agent.kernel

/-- Auditable verifier certificate for the static legitimacy instance. The
certificate carries a concrete extracted-graph audit subject and a computed
structural rejection theorem. The rejection witness is deliberately retained:
the GS-AI verifier component is not discharged by merely packaging the semantic
kernel predicate. -/
structure GovernanceAdmissibilityCertificate
    (world : StaticGovernanceWorldModel)
    (safety : SemanticLegitimacySafetySpec world) where
  auditSubject : AuditSubject
  rejectedCheck : AuditCheck
  verdict :
    governanceAdmissibilityVerdict auditSubject =
      AuditVerdict.rejected rejectedCheck

/-- Lighter certificate form for harnesses whose theorem surface is a concrete
check-status rejection rather than a top-level `governanceAdmissibilityVerdict`
rejection. This keeps the GS-AI bridge tied to executable audit evidence while
honestly preserving the exported theorem shape. -/
structure GovernanceAuditCheckCertificate where
  auditSubject : AuditSubject
  rejectedCheck : AuditCheck
  status : auditCheckStatus auditSubject rejectedCheck = .ok .failed

inductive GovernanceAuditEvidence
    (world : StaticGovernanceWorldModel)
    (safety : SemanticLegitimacySafetySpec world) where
  | admissibility :
      GovernanceAdmissibilityCertificate world safety →
        GovernanceAuditEvidence world safety
  | check :
      GovernanceAuditCheckCertificate →
        GovernanceAuditEvidence world safety

/-- Strengthened verifier-target object for the legitimacy GS-AI bridge.

Besides the governance-audit evidence, this object exposes the actual
kernelization extractor contract surface: the function-shaped contract, its two
branch-soundness obligations, and the five-constructor hidden-authority failure
vocabulary. The branch fields are deliberately projected at this level so the
GS-AI verifier is not merely the old admissibility certificate with a hidden
kernelization proof elsewhere. -/
structure GSAIKernelizationVerifier
    (world : StaticGovernanceWorldModel)
    (safety : SemanticLegitimacySafetySpec world) where
  auditEvidence : GovernanceAuditEvidence world safety
  artifact : Safety.RuleLayerKernelArtifact
  observation : Safety.GovernanceKernelizationObservation artifact
  contract : Safety.KernelizationExtractorContract observation
  cleanSound :
    ∀ input witness,
      contract.extract input = Sum.inl witness →
        Safety.KernelizationClean observation
  certSound :
    ∀ input cert,
      contract.extract input = Sum.inr cert →
        Safety.MinimalHiddenAuthority cert
  failureVocabulary :
    ∀ cert : Safety.HiddenAuthorityCertificate observation,
      Safety.HiddenAuthorityCertificateFromFiveKinds cert

/-- The explicit contract-surface predicate used by bridge theorems. It names
the three verifier-target components that the paper claims: function-shaped
`KernelizationExtractorContract`, clean/certificate branch soundness, and the
five-constructor hidden-authority failure vocabulary. -/
def GSAIKernelizationVerifier.contractSurface
    {world : StaticGovernanceWorldModel}
    {safety : SemanticLegitimacySafetySpec world}
    (verifier : GSAIKernelizationVerifier world safety) : Prop :=
  Nonempty (Safety.KernelizationExtractorContract verifier.observation) ∧
    (∀ input witness,
      verifier.contract.extract input = Sum.inl witness →
        Safety.KernelizationClean verifier.observation) ∧
      (∀ input cert,
        verifier.contract.extract input = Sum.inr cert →
          Safety.MinimalHiddenAuthority cert) ∧
        ∀ cert : Safety.HiddenAuthorityCertificate verifier.observation,
          Safety.HiddenAuthorityCertificateFromFiveKinds cert

theorem GSAIKernelizationVerifier.contractSurface_intro
    {world : StaticGovernanceWorldModel}
    {safety : SemanticLegitimacySafetySpec world}
    (verifier : GSAIKernelizationVerifier world safety)
    (cleanSound :
      ∀ input witness,
        verifier.contract.extract input = Sum.inl witness →
          Safety.KernelizationClean verifier.observation)
    (certSound :
      ∀ input cert,
        verifier.contract.extract input = Sum.inr cert →
          Safety.MinimalHiddenAuthority cert) :
    verifier.contractSurface :=
  ⟨⟨verifier.contract⟩, cleanSound, certSound,
    verifier.failureVocabulary⟩

/-- Our static-snapshot structural-governance instantiation of Dalrymple GS AI:
world model = static multi-agent governance snapshot with kernel-governed
trajectories, safety spec = per-agent semantic legitimacy kernels, verifier =
governance-audit evidence plus the kernelization extractor contract surface. -/
def legitimacyAsStaticGSAISnapshot : GuaranteedSafeAIInstance where
  worldModel := StaticGovernanceWorldModel
  safetySpec := SemanticLegitimacySafetySpec
  verifier := GSAIKernelizationVerifier

/-! ## Concrete non-vacuity fixture -/

/-- Compatible worked two-agent world with reflexive kernel trajectories for
each semantic-kernel agent. -/
noncomputable def compatibleTwoAgentStaticGovernanceWorld :
    StaticGovernanceWorldModel where
  system := compatibleTwoAgentSystem
  trajectories := by
    intro agent _hmem
    exact ⟨⟨agent.kernel, Safety.KernelGovernedTrajectory.refl agent.kernel⟩⟩

theorem compatibleTwoAgentStaticGovernanceWorld_semantic :
    SemanticLegitimacySafetySpec compatibleTwoAgentStaticGovernanceWorld := by
  intro agent hmem
  exact compatibleTwoAgentSystem_semantic agent hmem

/-- Concrete verifier witness: the Codex hooks extracted-governance fixture
emits a monotonicity rejection under the Lean port of the production
governance-admissibility audit. -/
def codexHooksMonotonicityGSAICertificate :
    GovernanceAdmissibilityCertificate
      compatibleTwoAgentStaticGovernanceWorld
      compatibleTwoAgentStaticGovernanceWorld_semantic where
  auditSubject := codexHooksExtractedGraph
  rejectedCheck := AuditCheck.monotonicity
  verdict := by
    simpa [codexHooksGovernanceAdmissibilityVerdict] using
      codexHooksGovernanceAdmissibilityRejectsMonotonicity

/-- Concrete verifier witness: the Claude Agent SDK extracted-governance
fixture emits the same production monotonicity rejection. -/
def claudeAgentSDKMonotonicityGSAICertificate :
    GovernanceAdmissibilityCertificate
      compatibleTwoAgentStaticGovernanceWorld
      compatibleTwoAgentStaticGovernanceWorld_semantic where
  auditSubject := claudeAgentSDKHooksExtractedGraph
  rejectedCheck := AuditCheck.monotonicity
  verdict := by
    simpa [claudeAgentSDKHooksGovernanceAdmissibilityVerdict] using
      claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicity

/-- Concrete verifier witness: the CrewAI extracted-governance fixture emits
a production monotonicity rejection. -/
def crewAIHooksMonotonicityGSAICertificate :
    GovernanceAdmissibilityCertificate
      compatibleTwoAgentStaticGovernanceWorld
      compatibleTwoAgentStaticGovernanceWorld_semantic where
  auditSubject := crewAIExtractedGraph
  rejectedCheck := AuditCheck.monotonicity
  verdict := by
    simpa [crewAIHooksGovernanceAdmissibilityVerdict] using
      crewAIHooksGovernanceAdmissibilityRejectsMonotonicity

/-- Concrete audit-check witness: the OpenClaw extracted-governance fixture
emits a production nonvacuity rejection. Its exported theorem is a check-status
fact, so this certificate records that exact surface rather than forcing an
expensive top-level verdict restatement in this bridge. -/
def openClawNonvacuityGSAICheckCertificate :
    GovernanceAuditCheckCertificate where
  auditSubject := openClawInfraExtractedGraph
  rejectedCheck := AuditCheck.nonvacuous
  status := openClawInfraNonvacuityCheckFails

/-- Canonical verifier-target packaging for this bridge's concrete
kernelization contract surface. The governance-audit evidence varies per
harness, while the kernelization surface is the committed function-shaped
contract from the kernelization examples with branch soundness and the
five-constructor hidden-authority vocabulary exposed as fields. -/
noncomputable def gsAIKernelizationVerifier
    (auditEvidence :
      GovernanceAuditEvidence
        compatibleTwoAgentStaticGovernanceWorld
        compatibleTwoAgentStaticGovernanceWorld_semantic) :
    GSAIKernelizationVerifier
      compatibleTwoAgentStaticGovernanceWorld
      compatibleTwoAgentStaticGovernanceWorld_semantic where
  auditEvidence := auditEvidence
  artifact := Safety.kernelizationExampleArtifact
  observation := Safety.cleanKernelizationObservation
  contract := Safety.cleanKernelizationExtractorContract
  cleanSound := Safety.cleanKernelizationExtractorContract.cleanSound
  certSound := Safety.cleanKernelizationExtractorContract.certSound
  failureVocabulary := Safety.hiddenAuthorityCertificate_from_five_kinds

/-- Strengthened verifier witness for the Codex hooks fixture. -/
noncomputable def codexHooksMonotonicityGSAIVerifier :
    GSAIKernelizationVerifier
      compatibleTwoAgentStaticGovernanceWorld
      compatibleTwoAgentStaticGovernanceWorld_semantic :=
  gsAIKernelizationVerifier
    (.admissibility codexHooksMonotonicityGSAICertificate)

/-- Strengthened verifier witness for the Claude Agent SDK fixture. -/
noncomputable def claudeAgentSDKMonotonicityGSAIVerifier :
    GSAIKernelizationVerifier
      compatibleTwoAgentStaticGovernanceWorld
      compatibleTwoAgentStaticGovernanceWorld_semantic :=
  gsAIKernelizationVerifier
    (.admissibility claudeAgentSDKMonotonicityGSAICertificate)

/-- Strengthened verifier witness for the CrewAI fixture. -/
noncomputable def crewAIHooksMonotonicityGSAIVerifier :
    GSAIKernelizationVerifier
      compatibleTwoAgentStaticGovernanceWorld
      compatibleTwoAgentStaticGovernanceWorld_semantic :=
  gsAIKernelizationVerifier
    (.admissibility crewAIHooksMonotonicityGSAICertificate)

/-- Strengthened verifier witness for the OpenClaw fixture. -/
noncomputable def openClawNonvacuityGSAIVerifier :
    GSAIKernelizationVerifier
      compatibleTwoAgentStaticGovernanceWorld
      compatibleTwoAgentStaticGovernanceWorld_semantic :=
  gsAIKernelizationVerifier
    (.check openClawNonvacuityGSAICheckCertificate)

/-- Named GS-AI certificate bundle for the committed leaderboard harness
fixtures. The fields are separate so the bridge cannot silently discharge the
multi-harness audit by reusing one certificate value four times. -/
structure GSAIHarnessCertificateBundle where
  codexHooks :
    GSAIKernelizationVerifier
      compatibleTwoAgentStaticGovernanceWorld
      compatibleTwoAgentStaticGovernanceWorld_semantic
  claudeAgentSDK :
    GSAIKernelizationVerifier
      compatibleTwoAgentStaticGovernanceWorld
      compatibleTwoAgentStaticGovernanceWorld_semantic
  crewAI :
    GSAIKernelizationVerifier
      compatibleTwoAgentStaticGovernanceWorld
      compatibleTwoAgentStaticGovernanceWorld_semantic
  openClaw :
    GSAIKernelizationVerifier
      compatibleTwoAgentStaticGovernanceWorld
      compatibleTwoAgentStaticGovernanceWorld_semantic
  codexHooks_contractSurface : codexHooks.contractSurface
  claudeAgentSDK_contractSurface : claudeAgentSDK.contractSurface
  crewAI_contractSurface : crewAI.contractSurface
  openClaw_contractSurface : openClaw.contractSurface

/-- The static GS-AI verifier slice is populated by concrete certificates from
Codex hooks, Claude Agent SDK, CrewAI, and OpenClaw fixtures, each packaged
against the strengthened kernelization verifier-target surface. -/
theorem gs_ai_fixture_certificates_cover_rejected_leaderboard_harnesses :
    Nonempty GSAIHarnessCertificateBundle :=
  ⟨{ codexHooks := codexHooksMonotonicityGSAIVerifier
     claudeAgentSDK := claudeAgentSDKMonotonicityGSAIVerifier
     crewAI := crewAIHooksMonotonicityGSAIVerifier
     openClaw := openClawNonvacuityGSAIVerifier
     codexHooks_contractSurface :=
       codexHooksMonotonicityGSAIVerifier.contractSurface_intro
         codexHooksMonotonicityGSAIVerifier.cleanSound
         codexHooksMonotonicityGSAIVerifier.certSound
     claudeAgentSDK_contractSurface :=
       claudeAgentSDKMonotonicityGSAIVerifier.contractSurface_intro
         claudeAgentSDKMonotonicityGSAIVerifier.cleanSound
         claudeAgentSDKMonotonicityGSAIVerifier.certSound
     crewAI_contractSurface :=
       crewAIHooksMonotonicityGSAIVerifier.contractSurface_intro
         crewAIHooksMonotonicityGSAIVerifier.cleanSound
         crewAIHooksMonotonicityGSAIVerifier.certSound
     openClaw_contractSurface :=
       openClawNonvacuityGSAIVerifier.contractSurface_intro
         openClawNonvacuityGSAIVerifier.cleanSound
         openClawNonvacuityGSAIVerifier.certSound }⟩

/-- Deprecated compatibility alias: the corrected name is
`gs_ai_fixture_certificates_cover_rejected_leaderboard_harnesses`, since the
bundle covers the four rejected leaderboard harness fixtures. -/
theorem gs_ai_fixture_certificates_cover_leaderboard_harnesses :
    Nonempty GSAIHarnessCertificateBundle :=
  gs_ai_fixture_certificates_cover_rejected_leaderboard_harnesses

/-- Headline static-snapshot bridge theorem. The legitimacy
structural-governance substrate is an instance of Dalrymple-style Guaranteed
Safe AI only on the static snapshot slice, and the verifier side is nonempty
for concrete fixtures because it invokes committed governance-admissibility
rejection theorems for Codex hooks, Claude Agent SDK, and CrewAI. The paired
harness-bundle theorem above additionally records OpenClaw's exported
nonvacuity check-status certificate. -/
theorem legitimacy_substrate_is_static_gs_ai_snapshot_instance :
    ∃ gs : GuaranteedSafeAIInstance,
      gs = legitimacyAsStaticGSAISnapshot ∧
        ∃ (world : StaticGovernanceWorldModel)
          (safety : SemanticLegitimacySafetySpec world),
          Nonempty (legitimacyAsStaticGSAISnapshot.verifier world safety) ∧
            ∃ verifier : GSAIKernelizationVerifier world safety,
              verifier.contractSurface := by
  refine ⟨legitimacyAsStaticGSAISnapshot, rfl, ?_⟩
  exact
    ⟨compatibleTwoAgentStaticGovernanceWorld,
      compatibleTwoAgentStaticGovernanceWorld_semantic,
      ⟨codexHooksMonotonicityGSAIVerifier⟩,
      codexHooksMonotonicityGSAIVerifier,
      codexHooksMonotonicityGSAIVerifier.contractSurface_intro
        codexHooksMonotonicityGSAIVerifier.cleanSound
        codexHooksMonotonicityGSAIVerifier.certSound⟩

end Legitimacy
