/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Safety.KernelSafety.GovernanceExamples

/-!
# Legitimacy.Safety.KernelSafety.StatefulExamples.Conclusions

Shared worked-example conclusion shapes for stateful kernel-safety examples.
-/

set_option autoImplicit false

namespace Legitimacy

namespace Safety

universe u v w

/-- Worked-example disjunction for subcritical stateful trajectories: either
bounded corrigibility is preserved, or a monitored aggregator sacrifice carries
the concrete critical-capability violation payload. -/
def WorkedSubcriticalConclusion
    {P : Type} [BinaryDecisionPipeline P]
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (adv : StatefulAdversaryLayer D)
    (schedule : List (StatefulScheduleStep D))
    (cfg : StatefulAdversaryConfig adv)
    {G pref tail : P} {node : BinaryDecisionPipeline.NodeOf P}
    (hagg : BinaryDecisionPipeline.IsPeerRelativeAggregator node)
    (heffective :
      BinaryDecisionPipeline.EffectiveSurfaceForNode node G pref tail)
    (hcomplete : BinaryDecisionPipeline.CompleteTailForNode node tail) :
    Prop :=
  BoundedCorrigibilityPreservedAt D adv schedule cfg ∨
    ∃ cert : MonitoredSacrificeCertificate D D,
      AggregatorAxiomWitnessedSacrifice cert hagg heffective hcomplete ∧
      ∃ hcritical :
        kernelDataCriticalCapability D ≤
          statefulTrajectoryPerturbationBound D adv schedule cfg,
        cert.stateful_violation =
          some
            ({ adv := adv
               schedule := schedule
               cfg := cfg
               critical_le_budget := hcritical } :
              StatefulCriticalCapabilityViolation D)

/-- Certificate-level worked-example conclusion for supercritical consistency
routes: the certificate has the route witness and carries the concrete
critical-capability violation payload. -/
def WorkedSupercriticalConclusion
    {P : Type} [BinaryDecisionPipeline P]
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (adv : StatefulAdversaryLayer D)
    (schedule : List (StatefulScheduleStep D))
    (cfg : StatefulAdversaryConfig adv)
    {G pref tail : P} {node : BinaryDecisionPipeline.NodeOf P}
    (cert : MonitoredSacrificeCertificate D D)
    (hwitness : BinaryDecisionPipeline.HasConsistencyViolationWitness node)
    (heffective :
      BinaryDecisionPipeline.EffectiveSurfaceForNode node G pref tail)
    (hcomplete : BinaryDecisionPipeline.CompleteTailForNode node tail) :
    Prop :=
  ConsistencyAxiomWitnessedSacrifice cert hwitness heffective hcomplete ∧
    ∃ hcritical :
      kernelDataCriticalCapability D ≤
        statefulTrajectoryPerturbationBound D adv schedule cfg,
      cert.stateful_violation =
        some
          ({ adv := adv
             schedule := schedule
             cfg := cfg
             critical_le_budget := hcritical } :
            StatefulCriticalCapabilityViolation D)

end Safety

end Legitimacy
