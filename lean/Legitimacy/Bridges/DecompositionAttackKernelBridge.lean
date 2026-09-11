/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Protocol.CompiledStepPolicy
import Legitimacy.Safety.KernelSafety.Sacrifice

/-!
# Decomposition-attack monitor retagging

This module is a narrow compatibility bridge. Given already-emitted monitor
evidence and a canonical claim decomposition evaluated by that certificate's
compiled graph, it can retag the monitoring event as compositional safety.

It does not bind claims to kernel actions, prove replay simulation, or produce
a `KernelAxiomViolation`.
-/

set_option autoImplicit false

namespace Legitimacy

open Safety

namespace Safety.MonitoredSacrificeCertificate

/-- Retag already-emitted monitor evidence using a claim decomposition whose
local and composed verdicts both come from the certificate's compiled graph.
The existing transition and monitoring payload are preserved. -/
noncomputable def retagCompositionalSafetyOfCompiledClaimAttack
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (certificate : MonitoredSacrificeCertificate D D')
    (hattack : certificate.compiled.ClaimDecompositionAttack) :
    MonitoredSacrificeCertificate D D' where
  sacrificed := SacrificedAxiom.kernel KernelAxiom.CompositionalSafety
  step := certificate.step
  claim_profile := certificate.claim_profile
  claimant := certificate.claimant
  aggregator_witness := certificate.aggregator_witness
  stateful_violation := certificate.stateful_violation
  compiled := certificate.compiled
  monitoring := certificate.monitoring
  graph_bound := certificate.graph_bound
  monitoring_obligation :=
    { fires :=
        LocalPermissionMonotonicity
          CompiledGovernance.appendClaim []
          certificate.compiled.claimStepNode
          certificate.compiled.composedClaimsDenied
      decidable_fires := by
        classical
        infer_instance
      fired :=
        CompiledGovernance.claimDecompositionAttack_localPermissionFailure
          certificate.compiled hattack
      bound_exceedance :=
        certificate.monitoring_obligation.bound_exceedance
      runtime_observation :=
        MonitoringRuntimeObservation.ofSacrifice
          (SacrificedAxiom.kernel KernelAxiom.CompositionalSafety)
          certificate.compiled certificate.monitoring
      ledger_emission :=
        MonitoringLedgerEmission.ofSacrifice
          (SacrificedAxiom.kernel KernelAxiom.CompositionalSafety)
          certificate.compiled certificate.monitoring }

end Safety.MonitoredSacrificeCertificate

/-- Already-emitted monitor evidence can be retagged when each emitted
certificate's compiled graph admits the canonical claim attack. This theorem
does not assert that the raw step realizes the claim sequence. -/
theorem compiledClaimAttack_monitorRetag_ofMonitorEvidence
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (step : RawKernelStep D D')
    (hmonitor : RawKernelStep.MonitorHypothesis step)
    (hattack :
      ∀ emitted : MonitoredSacrificeCertificate D D',
        emitted.compiled.ClaimDecompositionAttack) :
    ∃ retagged : MonitoredSacrificeCertificate D D',
      retagged.sacrificed =
        SacrificedAxiom.kernel KernelAxiom.CompositionalSafety := by
  rcases hmonitor with ⟨emitted⟩
  exact
    ⟨emitted.retagCompositionalSafetyOfCompiledClaimAttack
        (hattack emitted),
      rfl⟩

end Legitimacy
