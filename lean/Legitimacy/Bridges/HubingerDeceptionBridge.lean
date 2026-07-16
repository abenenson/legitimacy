/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Audits.SleeperCharacterization

/-!
# Hubinger learned-deception bridge

This module gives a narrow structural bridge to Hubinger, van Merwijk,
Mikulik, Skalse, and Garrabrant, "Risks from Learned Optimization in Advanced
Machine Learning Systems" (arXiv:1906.01820, 2019; revised 2021), and to
Hubinger et al., "Sleeper Agents: Training Deceptive LLMs that Persist Through
Safety Training" (arXiv:2401.05566, 2024).

The claim is only about the slice represented in this repository: extracted
governance audit subjects with a dormant training trigger and a deployment
trigger whose positive perturbation changes a monitored claimant from permit
to deny. It is not a full formalization of mesa-optimization, learned
objectives, or all deceptive-alignment models.
-/

set_option autoImplicit false

namespace Legitimacy

/-- The represented Hubinger-style slice: an extracted audit subject that has
one training trigger, one deployment trigger, a concrete deceptive-deployment
witness, and a conventional audit check that still passes pre-trigger. -/
structure HubingerDeceptionScenario where
  subject : AuditSubject
  trainingTrigger : AuditMetricField
  deploymentTrigger : AuditMetricField
  deployment_split :
    AdmitsDeceptiveDeployment subject trainingTrigger deploymentTrigger
  pretrigger_compositionalSafety :
    auditCheckStatus subject AuditCheck.compositionalSafety = .ok .passed

/-- The corresponding legitimacy substrate witness: the scenario is an
extracted-governance sleeper split and therefore obstructs audit monotonicity
on the synthesized finite claim corpus. -/
structure KernelSleeperSubstrateWitness
    (scenario : HubingerDeceptionScenario) where
  audit_passes_pretrigger :
    auditCheckStatus scenario.subject AuditCheck.compositionalSafety =
      .ok .passed
  sleeper_triggered :
    AdmitsDeceptiveDeployment scenario.subject scenario.trainingTrigger
      scenario.deploymentTrigger
  monotonicity_obstruction :
    ¬ AuditGraphMonotonicity scenario.subject
      (auditGraphClaims scenario.subject)

/-- Hubinger learned-deception bridge on the represented sleeper-audit slice.
The proof uses the existing sleeper-characterization theorem converting a
deployment-trigger split into a monotonicity obstruction; it is not a
definitional pass-through from the scenario fields. -/
theorem hubinger_deception_subsumed_by_kernel_substrate
    (scenario : HubingerDeceptionScenario) :
    KernelSleeperSubstrateWitness scenario := by
  exact
    { audit_passes_pretrigger := scenario.pretrigger_compositionalSafety
      sleeper_triggered := scenario.deployment_split
      monotonicity_obstruction :=
        deceptive_deployment_not_audit_monotone scenario.deployment_split }

/-- Tightness fixture: the committed sleeper-agent extracted graph realizes
the represented Hubinger-style deployment split. -/
def sleeperAgentHubingerScenario : HubingerDeceptionScenario where
  subject := sleeperAgentExtractedGraph
  trainingTrigger := "training_context"
  deploymentTrigger := "deployment_context"
  deployment_split := sleeperAgentAdmitsDeceptiveDeployment
  pretrigger_compositionalSafety := sleeperAgentPassesCompositionalSafety

theorem sleeper_agent_hubinger_bridge_witness :
    KernelSleeperSubstrateWitness sleeperAgentHubingerScenario :=
  hubinger_deception_subsumed_by_kernel_substrate
    sleeperAgentHubingerScenario

/-- Drop-test: a sleeper-shaped graph with a deployment router but no harmful
terminal effect is rejected by the represented bridge predicate. -/
theorem inert_sleeper_shape_not_hubinger_deception_scenario :
    ¬ AdmitsDeceptiveDeployment inertSleeperAttemptSubject
      "training_context" "deployment_context" :=
  inertSleeperShapedAttack_rejects_deceptive_deployment

end Legitimacy
