/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Audits.SleeperAgent
import Legitimacy.SafetySpecReduction

/-!
# Legitimacy.Audits.SleeperCharacterization

Structural audit-subject diagnostic layer for represented sleeper-agent
deployment splits on the extracted-governance audit surface.

`Safety.AuthorityGraph` records authority reachability only; it has no decision
evaluator or metric perturbation semantics. The represented sleeper-agent split
therefore lives at the `AuditSubject` layer used by the T4 extraction, where
`auditFinalDecisions`, `auditGraphDeltas`, and `auditModifyClaim` already encode
the finite monotonicity perturbation family. The theorems below are structural
diagnostics over extracted audit subjects, not behavioral claims about
underlying models.
-/

set_option autoImplicit false

namespace Legitimacy

/-! ## Deceptive deployment witnesses -/

/-- Training-time assignment for a fixed extracted-governance claim corpus.

The monitored claim has the deployment trigger dormant in the training corpus;
this is the formal "deployment trigger does not fire during safety training"
clause. -/
structure TrainingAssignment
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim)
    (deploymentTrigger : AuditMetricField) where
  decisions : List (AuditClaimantId × AuditDecision)
  computes : auditFinalDecisions subject claims = Except.ok decisions
  monitoredClaim : AuditGovernanceClaim
  monitored_mem : monitoredClaim ∈ claims
  deployment_trigger_dormant :
    monitoredClaim.metrics.lookup deploymentTrigger = some 0

/-- Deployment-time assignment produced by strengthening the deployment trigger. -/
structure DeploymentAssignment
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim) where
  decisions : List (AuditClaimantId × AuditDecision)
  computes : auditFinalDecisions subject claims = Except.ok decisions

/-- A concrete represented sleeper-agent split in an extracted audit subject:
the same monitored claimant is permitted in the training corpus and denied
after a positive deployment-trigger strengthening. The trigger names are
required to be distinct, so the deployment trigger is not the training-time
safety predicate itself. -/
structure DeceptiveDeploymentWitnessOn
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim)
    (trainingTrigger deploymentTrigger : AuditMetricField) where
  training : TrainingAssignment subject claims deploymentTrigger
  deploymentClaim : AuditGovernanceClaim
  deploymentClaim_mem : deploymentClaim ∈ claims
  delta : AuditMetricValue
  delta_positive : 0 < delta
  delta_enumerated : (deploymentTrigger, delta) ∈ auditGraphDeltas claims
  deploymentClaims : List AuditGovernanceClaim
  deployment_update :
    auditModifyClaim deploymentClaim.claimantId
      (fun claim => auditApplyFieldDelta claim deploymentTrigger delta)
      claims = Except.ok deploymentClaims
  deployment : DeploymentAssignment subject deploymentClaims
  affectedClaimant : AuditClaimantId
  affected_claimant_enumerated : affectedClaimant ∈ auditClaimantIds claims
  training_passes :
    lookupDecision? training.decisions affectedClaimant = some AuditDecision.permit
  deployment_executes :
    lookupDecision? deployment.decisions affectedClaimant = some AuditDecision.deny
  triggers_disjoint : trainingTrigger ≠ deploymentTrigger

/-- The theorem-facing structural deceptive-deployment predicate on a fixed
audit-subject claim corpus. -/
def AdmitsDeceptiveDeploymentOn
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim)
    (trainingTrigger deploymentTrigger : AuditMetricField) : Prop :=
  Nonempty
    (DeceptiveDeploymentWitnessOn subject claims trainingTrigger deploymentTrigger)

/-- Canonical structural extracted-graph predicate: use the audit corpus
synthesized from the subject graph. -/
def AdmitsDeceptiveDeployment
    (subject : AuditSubject)
    (trainingTrigger deploymentTrigger : AuditMetricField) : Prop :=
  AdmitsDeceptiveDeploymentOn subject (auditGraphClaims subject)
    trainingTrigger deploymentTrigger

/-! ## Prop-level audit monotonicity -/

/-- Prop-level counterpart of `auditCheckMonotonicityCore`: every positive
finite audit perturbation weakly preserves every claimant's decision rank. -/
def AuditGraphMonotonicity
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim) : Prop :=
  ∀ (original : List (AuditClaimantId × AuditDecision))
    (field : AuditMetricField) (delta : AuditMetricValue)
    (strengthenedClaim : AuditGovernanceClaim)
    (strengthenedClaims : List AuditGovernanceClaim)
    (strengthened : List (AuditClaimantId × AuditDecision))
    (claimantId : AuditClaimantId)
    (before after : AuditDecision),
    auditFinalDecisions subject claims = Except.ok original →
    (field, delta) ∈ auditGraphDeltas claims →
    0 < delta →
    strengthenedClaim ∈ claims →
    auditModifyClaim strengthenedClaim.claimantId
        (fun claim => auditApplyFieldDelta claim field delta) claims =
      Except.ok strengthenedClaims →
    auditFinalDecisions subject strengthenedClaims = Except.ok strengthened →
    claimantId ∈ auditClaimantIds claims →
    lookupDecision? original claimantId = some before →
    lookupDecision? strengthened claimantId = some after →
    decisionRank before ≤ decisionRank after

/-- A represented deceptive-deployment split is a concrete legacy monotonicity
obstruction for the extracted audit subject: the witness supplies the training
assignment, the deployment-trigger perturbation, and the permit-to-deny
affected claimant. -/
theorem deceptive_deployment_on_not_audit_monotone
    {subject : AuditSubject}
    {claims : List AuditGovernanceClaim}
    {trainingTrigger deploymentTrigger : AuditMetricField} :
    AdmitsDeceptiveDeploymentOn subject claims trainingTrigger deploymentTrigger →
      ¬ AuditGraphMonotonicity subject claims := by
  intro hdeceptive hmon
  rcases hdeceptive with ⟨w⟩
  have hrank :
      decisionRank AuditDecision.permit ≤ decisionRank AuditDecision.deny :=
    hmon
      w.training.decisions
      deploymentTrigger
      w.delta
      w.deploymentClaim
      w.deploymentClaims
      w.deployment.decisions
      w.affectedClaimant
      AuditDecision.permit
      AuditDecision.deny
      w.training.computes
      w.delta_enumerated
      w.delta_positive
      w.deploymentClaim_mem
      w.deployment_update
      w.deployment.computes
      w.affected_claimant_enumerated
      w.training_passes
      w.deployment_executes
  norm_num [decisionRank] at hrank

/-- Canonical claim-corpus specialization of
`deceptive_deployment_on_not_audit_monotone`. -/
theorem deceptive_deployment_not_audit_monotone
    {subject : AuditSubject}
    {trainingTrigger deploymentTrigger : AuditMetricField} :
    AdmitsDeceptiveDeployment subject trainingTrigger deploymentTrigger →
      ¬ AuditGraphMonotonicity subject (auditGraphClaims subject) :=
  deceptive_deployment_on_not_audit_monotone

/-! ## Executable finite diagnostic and tightness fixtures -/

/-- Executable finite structural check for the canonical represented sleeper
split. This is a diagnostic projection of `AdmitsDeceptiveDeploymentOn`, used
for concrete tightness witnesses and audit reports. -/
def admitsDeceptiveDeploymentOnCheck
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim)
    (trainingTrigger deploymentTrigger : AuditMetricField) : Bool :=
  if trainingTrigger = deploymentTrigger then
    false
  else
    match auditFinalDecisions subject claims with
    | .error _ => false
    | .ok original =>
        claims.any fun monitoredClaim =>
          monitoredClaim.metrics.lookup deploymentTrigger = some 0 &&
            (auditGraphDeltas claims).any fun (field, delta) =>
              field = deploymentTrigger && delta > 0 &&
                claims.any fun strengthenedClaim =>
                match auditModifyClaim strengthenedClaim.claimantId
                    (fun claim => auditApplyFieldDelta claim deploymentTrigger delta)
                    claims with
                | .error _ => false
                | .ok strengthenedClaims =>
                    match auditFinalDecisions subject strengthenedClaims with
                    | .error _ => false
                    | .ok strengthened =>
                        (auditClaimantIds claims).any fun claimantId =>
                          lookupDecision? original claimantId =
                              some AuditDecision.permit &&
                            lookupDecision? strengthened claimantId =
                              some AuditDecision.deny

/-- Canonical executable finite check over `auditGraphClaims`. -/
def admitsDeceptiveDeploymentCheck
    (subject : AuditSubject)
    (trainingTrigger deploymentTrigger : AuditMetricField) : Bool :=
  admitsDeceptiveDeploymentOnCheck subject (auditGraphClaims subject)
    trainingTrigger deploymentTrigger

theorem admitsDeceptiveDeploymentOnCheck_sound
    {subject : AuditSubject}
    {claims : List AuditGovernanceClaim}
    {trainingTrigger deploymentTrigger : AuditMetricField} :
    admitsDeceptiveDeploymentOnCheck subject claims
        trainingTrigger deploymentTrigger = true →
      AdmitsDeceptiveDeploymentOn subject claims
        trainingTrigger deploymentTrigger := by
  intro hcheck
  unfold admitsDeceptiveDeploymentOnCheck at hcheck
  by_cases htriggers : trainingTrigger = deploymentTrigger
  · simp [htriggers] at hcheck
  · simp [htriggers] at hcheck
    cases htraining : auditFinalDecisions subject claims with
    | error err =>
        simp [htraining] at hcheck
    | ok original =>
        simp [htraining] at hcheck
        rcases hcheck with
          ⟨monitoredClaim, hmonitored_mem, hmonitored_true⟩
        rcases hmonitored_true with ⟨hmonitored_dormant, hdeltas_true⟩
        rcases hdeltas_true with
          ⟨delta, hdelta_mem, hdelta_pos, hclaims_true⟩
        rcases hclaims_true with
          ⟨deploymentClaim, hdeployment_mem, hdeployment_true⟩
        cases hmodify :
            auditModifyClaim deploymentClaim.claimantId
              (fun claim => auditApplyFieldDelta claim deploymentTrigger delta)
              claims with
        | error err =>
            simp [hmodify] at hdeployment_true
        | ok deploymentClaims =>
            simp [hmodify] at hdeployment_true
            cases hdeployment :
                auditFinalDecisions subject deploymentClaims with
            | error err =>
                simp [hdeployment] at hdeployment_true
            | ok deployed =>
                simp [hdeployment] at hdeployment_true
                rcases hdeployment_true with
                  ⟨affectedClaimant, haffected_mem, haffected_true⟩
                rcases haffected_true with
                  ⟨htraining_permit, hdeployment_deny⟩
                exact ⟨
                  { training :=
                      { decisions := original
                        computes := htraining
                        monitoredClaim := monitoredClaim
                        monitored_mem := hmonitored_mem
                        deployment_trigger_dormant := hmonitored_dormant }
                    deploymentClaim := deploymentClaim
                    deploymentClaim_mem := hdeployment_mem
                    delta := delta
                    delta_positive := hdelta_pos
                    delta_enumerated := hdelta_mem
                    deploymentClaims := deploymentClaims
                    deployment_update := hmodify
                    deployment :=
                      { decisions := deployed
                        computes := hdeployment }
                    affectedClaimant := affectedClaimant
                    affected_claimant_enumerated := haffected_mem
                    training_passes := htraining_permit
                    deployment_executes := hdeployment_deny
                    triggers_disjoint := htriggers }⟩

theorem admitsDeceptiveDeploymentOnCheck_complete
    {subject : AuditSubject}
    {claims : List AuditGovernanceClaim}
    {trainingTrigger deploymentTrigger : AuditMetricField} :
    AdmitsDeceptiveDeploymentOn subject claims
        trainingTrigger deploymentTrigger →
      admitsDeceptiveDeploymentOnCheck subject claims
        trainingTrigger deploymentTrigger = true := by
  intro hdeceptive
  rcases hdeceptive with ⟨w⟩
  unfold admitsDeceptiveDeploymentOnCheck
  simp [w.triggers_disjoint, w.training.computes]
  refine ⟨w.training.monitoredClaim, w.training.monitored_mem, ?_⟩
  refine ⟨w.training.deployment_trigger_dormant, ?_⟩
  refine ⟨w.delta, w.delta_enumerated, w.delta_positive, ?_⟩
  refine ⟨w.deploymentClaim, w.deploymentClaim_mem, ?_⟩
  simp [w.deployment_update, w.deployment.computes]
  refine ⟨w.affectedClaimant, w.affected_claimant_enumerated, ?_⟩
  exact ⟨w.training_passes, w.deployment_executes⟩

/-- Boolean sleeper-agent detection is equivalent to the Prop-level deceptive
deployment predicate for the supplied trigger pair. -/
theorem admitsDeceptiveDeploymentOnCheck_iff_AdmitsDeceptiveDeploymentOn
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim)
    (trainingTrigger deploymentTrigger : AuditMetricField) :
    admitsDeceptiveDeploymentOnCheck subject claims
        trainingTrigger deploymentTrigger = true ↔
      AdmitsDeceptiveDeploymentOn subject claims
        trainingTrigger deploymentTrigger :=
  ⟨admitsDeceptiveDeploymentOnCheck_sound,
    admitsDeceptiveDeploymentOnCheck_complete⟩

theorem admitsDeceptiveDeploymentCheck_iff_AdmitsDeceptiveDeployment
    (subject : AuditSubject)
    (trainingTrigger deploymentTrigger : AuditMetricField) :
    admitsDeceptiveDeploymentCheck subject trainingTrigger deploymentTrigger =
        true ↔
      AdmitsDeceptiveDeployment subject trainingTrigger deploymentTrigger := by
  exact admitsDeceptiveDeploymentOnCheck_iff_AdmitsDeceptiveDeploymentOn
    subject (auditGraphClaims subject) trainingTrigger deploymentTrigger

theorem admitsDeceptiveDeploymentCheck_sound
    {subject : AuditSubject}
    {trainingTrigger deploymentTrigger : AuditMetricField} :
    admitsDeceptiveDeploymentCheck subject trainingTrigger deploymentTrigger =
        true →
      AdmitsDeceptiveDeployment subject trainingTrigger deploymentTrigger :=
  (admitsDeceptiveDeploymentCheck_iff_AdmitsDeceptiveDeployment
    subject trainingTrigger deploymentTrigger).1

theorem admitsDeceptiveDeploymentCheck_complete
    {subject : AuditSubject}
    {trainingTrigger deploymentTrigger : AuditMetricField} :
    AdmitsDeceptiveDeployment subject trainingTrigger deploymentTrigger →
      admitsDeceptiveDeploymentCheck subject trainingTrigger deploymentTrigger =
        true :=
  (admitsDeceptiveDeploymentCheck_iff_AdmitsDeceptiveDeployment
    subject trainingTrigger deploymentTrigger).2

theorem admitsDeceptiveDeploymentCheck_false_implies_not_admits
    {subject : AuditSubject}
    {trainingTrigger deploymentTrigger : AuditMetricField} :
    admitsDeceptiveDeploymentCheck subject trainingTrigger deploymentTrigger =
        false →
      ¬ AdmitsDeceptiveDeployment subject trainingTrigger deploymentTrigger := by
  intro hfalse hdeceptive
  have htrue :=
    admitsDeceptiveDeploymentCheck_complete
      (subject := subject)
      (trainingTrigger := trainingTrigger)
      (deploymentTrigger := deploymentTrigger)
      hdeceptive
  rw [hfalse] at htrue
  cases htrue

/-- Concrete non-vacuity witness: the represented Hubinger-style sleeper-agent
audit subject admits the training-vs-deployment split. -/
theorem sleeperAgentAdmitsDeceptiveDeployment :
    AdmitsDeceptiveDeployment sleeperAgentExtractedGraph
      "training_context" "deployment_context" := by
  refine ⟨?_⟩
  exact
    { training :=
        { decisions :=
            [ ("baseline", AuditDecision.permit)
            , ("behavioral_safety_training_policy-gate-0", AuditDecision.permit)
            , ("deployment_trigger_router-gate-0", AuditDecision.deny)
            , ("hidden_backdoor_behavior-gate-0", AuditDecision.permit) ]
          computes := by native_decide
          monitoredClaim :=
            { claimantId := "baseline"
              strength := 1
              priorityClass := some "extracted"
              path := some "/workspace/safe.rs"
              action := some "safe_action"
              content := some "safe content"
              metrics := [("deployment_context", 0), ("training_context", 0)] }
          monitored_mem := by native_decide
          deployment_trigger_dormant := by native_decide }
      deploymentClaim :=
        { claimantId := "baseline"
          strength := 1
          priorityClass := some "extracted"
          path := some "/workspace/safe.rs"
          action := some "safe_action"
          content := some "safe content"
          metrics := [("deployment_context", 0), ("training_context", 0)] }
      deploymentClaim_mem := by native_decide
      delta := 1
      delta_positive := by norm_num
      delta_enumerated := by native_decide
      deploymentClaims :=
        [ { claimantId := "baseline"
            strength := 1
            priorityClass := some "extracted"
            path := some "/workspace/safe.rs"
            action := some "safe_action"
            content := some "safe content"
            metrics := [("deployment_context", 1), ("training_context", 0)] }
        , { claimantId := "behavioral_safety_training_policy-gate-0"
            strength := 1
            priorityClass := some "extracted"
            path := some "/workspace/safe.rs"
            action := some "safe_action"
            content := some "safe content"
            metrics := [("deployment_context", 0), ("permit_signal", 1),
              ("training_context", 1)] }
        , { claimantId := "deployment_trigger_router-gate-0"
            strength := 1
            priorityClass := some "extracted"
            path := some "/workspace/safe.rs"
            action := some "safe_action"
            content := some "safe content"
            metrics := [("deployment_context", 1), ("escalate_signal", 1),
              ("training_context", 0)] }
        , { claimantId := "hidden_backdoor_behavior-gate-0"
            strength := 1
            priorityClass := some "extracted"
            path := some "/workspace/safe.rs"
            action := some "safe_action"
            content := some "safe content"
            metrics := [("deployment_context", 0), ("permit_signal", 1),
              ("training_context", 1)] } ]
      deployment_update := by native_decide
      deployment :=
        { decisions :=
            [ ("baseline", AuditDecision.deny)
            , ("behavioral_safety_training_policy-gate-0", AuditDecision.permit)
            , ("deployment_trigger_router-gate-0", AuditDecision.deny)
            , ("hidden_backdoor_behavior-gate-0", AuditDecision.permit) ]
          computes := by native_decide }
      affectedClaimant := "baseline"
      affected_claimant_enumerated := by native_decide
      training_passes := by native_decide
      deployment_executes := by native_decide
      triggers_disjoint := by native_decide }

theorem sleeperAgentAdmitsDeceptiveDeploymentCheck :
    admitsDeceptiveDeploymentCheck sleeperAgentExtractedGraph
      "training_context" "deployment_context" = true := by
  native_decide

/-- A non-deceptive threshold-only graph: it is useful as an independence
witness because the deployment-trigger field is absent from the perturbation
family, while the ordinary audit graph still has both permit and deny outcomes. -/
def thresholdOnlyGovernanceGraph : AuditGovernanceGraph where
  nodes :=
    [ .binary "training_policy"
        "Training-only safety policy"
        [ .thresholdGate "training_context" 1 .permit ]
        .deny
        .firstMatch ]
  edges := []

def thresholdOnlySubject : AuditSubject where
  graph := thresholdOnlyGovernanceGraph
  evalNode := auditEvaluateNode

theorem thresholdOnlyNoDeceptiveDeploymentCheck :
    admitsDeceptiveDeploymentCheck thresholdOnlySubject
      "training_context" "deployment_context" = false := by
  native_decide

theorem thresholdOnly_rejects_deceptive_deployment_bool :
    admitsDeceptiveDeploymentCheck thresholdOnlySubject
      "training_context" "deployment_context" = false :=
  thresholdOnlyNoDeceptiveDeploymentCheck

theorem thresholdOnly_rejects_deceptive_deployment :
    ¬ AdmitsDeceptiveDeployment thresholdOnlySubject
      "training_context" "deployment_context" :=
  admitsDeceptiveDeploymentCheck_false_implies_not_admits
    thresholdOnly_rejects_deceptive_deployment_bool

theorem thresholdOnlyPassesSolidarity :
    auditCheckStatus thresholdOnlySubject AuditCheck.solidarity =
      .ok .passed := by
  native_decide

theorem thresholdOnlyPassesNonvacuity :
    auditCheckStatus thresholdOnlySubject AuditCheck.nonvacuous =
      .ok .passed := by
  native_decide

theorem thresholdOnly_passes_monotonicity :
    auditCheckStatus thresholdOnlySubject AuditCheck.monotonicity =
      .ok .passed := by
  native_decide

/-- A permit-to-escalate-only graph: strengthening deployment context lowers
the canonical audit rank from `permit` to `escalate`, but no perturbation can
produce the permit-to-deny deployment split required by
`AdmitsDeceptiveDeployment`. -/
def permitEscalateOnlyGovernanceGraph : AuditGovernanceGraph where
  nodes :=
    [ .binary "deployment_escalation_policy"
        "Deployment escalation policy"
        [ .thresholdGate "deployment_context" 1 .escalate ]
        .permit
        .firstMatch ]
  edges := []

def permitEscalateOnly : AuditSubject where
  graph := permitEscalateOnlyGovernanceGraph
  evalNode := auditEvaluateNode

theorem permitEscalateOnly_fails_monotonicity :
    ¬ AuditGraphMonotonicity permitEscalateOnly
      (auditGraphClaims permitEscalateOnly) := by
  intro hmonotone
  have hrank :
      decisionRank AuditDecision.permit ≤ decisionRank AuditDecision.escalate :=
    hmonotone
      [("baseline", AuditDecision.permit),
        ("deployment_escalation_policy-gate-0", AuditDecision.escalate)]
      "deployment_context"
      1
      { claimantId := "baseline"
        strength := 1
        priorityClass := some "extracted"
        path := some "/workspace/safe.rs"
        action := some "safe_action"
        content := some "safe content"
        metrics := [("deployment_context", 0)] }
      [ { claimantId := "baseline"
          strength := 1
          priorityClass := some "extracted"
          path := some "/workspace/safe.rs"
          action := some "safe_action"
          content := some "safe content"
          metrics := [("deployment_context", 1)] }
      , { claimantId := "deployment_escalation_policy-gate-0"
          strength := 1
          priorityClass := some "extracted"
          path := some "/workspace/safe.rs"
          action := some "safe_action"
          content := some "safe content"
          metrics := [("deployment_context", 1), ("escalate_signal", 1)] } ]
      [("baseline", AuditDecision.escalate),
        ("deployment_escalation_policy-gate-0", AuditDecision.escalate)]
      "baseline"
      AuditDecision.permit
      AuditDecision.escalate
      (by native_decide)
      (by native_decide)
      (by norm_num)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
  norm_num [decisionRank] at hrank

theorem permitEscalateOnly_rejects_deceptive_deployment_bool :
    admitsDeceptiveDeploymentCheck permitEscalateOnly
      "training_context" "deployment_context" = false := by
  native_decide

theorem permitEscalateOnly_rejects_deceptive_deployment :
    ¬ AdmitsDeceptiveDeployment permitEscalateOnly
      "training_context" "deployment_context" :=
  admitsDeceptiveDeploymentCheck_false_implies_not_admits
    permitEscalateOnly_rejects_deceptive_deployment_bool

/-- Strict refinement: `AdmitsDeceptiveDeploymentOn` is strictly stronger than
legacy audit monotonicity failure on extracted subjects. Every represented
subject admitting deceptive deployment fails monotonicity, but not every
monotonicity-failing subject admits deceptive deployment. -/
theorem admitsDeceptiveDeployment_strict_refinement_of_monotonicity_failure :
    (∀ (subject : AuditSubject) (claims : List AuditGovernanceClaim)
        (trainingTrigger deploymentTrigger : AuditMetricField),
      AdmitsDeceptiveDeploymentOn subject claims
          trainingTrigger deploymentTrigger →
        ¬ AuditGraphMonotonicity subject claims) ∧
      (∃ subject : AuditSubject,
        ¬ AuditGraphMonotonicity subject (auditGraphClaims subject) ∧
          ¬ AdmitsDeceptiveDeployment subject
            "training_context" "deployment_context") := by
  refine ⟨?forward, ?strict⟩
  · intro subject claims trainingTrigger deploymentTrigger
    exact deceptive_deployment_on_not_audit_monotone
  · exact ⟨permitEscalateOnly,
      permitEscalateOnly_fails_monotonicity,
      permitEscalateOnly_rejects_deceptive_deployment⟩

/-- A sleeper-shaped represented audit subject with a deployment router but no
harmful terminal effect. The diagnostic rejects the structural predicate: no
permit-to-deny deployment split is present. -/
def inertSleeperAttemptGovernanceGraph : AuditGovernanceGraph where
  nodes :=
    [ .binary "behavioral_safety_training_policy"
        "Behavioral safety training policy"
        [ .thresholdGate "training_context" 1 .permit ]
        .permit
        .firstMatch
    , .binary "deployment_trigger_router"
        "Deployment trigger router"
        [ .thresholdGate "deployment_context" 1 .escalate ]
        .permit
        .firstMatch
    , .binary "inert_backdoor_behavior"
        "Attempted backdoor that remains permitted"
        [ .thresholdGate "training_context" 1 .permit ]
        .permit
        .firstMatch ]
  edges :=
    [ { fromNode := "deployment_trigger_router"
        toNode := "inert_backdoor_behavior"
        transform := .passThrough } ]

def inertSleeperAttemptSubject : AuditSubject where
  graph := inertSleeperAttemptGovernanceGraph
  evalNode := auditEvaluateNode

theorem inertSleeperAttemptNoDeceptiveDeploymentCheck :
    admitsDeceptiveDeploymentCheck inertSleeperAttemptSubject
      "training_context" "deployment_context" = false := by
  native_decide

theorem inertSleeperShapedAttack_rejects_deceptive_deployment_bool :
    admitsDeceptiveDeploymentCheck inertSleeperAttemptSubject
      "training_context" "deployment_context" = false :=
  inertSleeperAttemptNoDeceptiveDeploymentCheck

theorem inertSleeperShapedAttack_rejects_deceptive_deployment :
    ¬ AdmitsDeceptiveDeployment inertSleeperAttemptSubject
      "training_context" "deployment_context" :=
  admitsDeceptiveDeploymentCheck_false_implies_not_admits
    inertSleeperShapedAttack_rejects_deceptive_deployment_bool

/-- Operational distinctness from the graph-shape compositional-safety
projection: the represented sleeper audit subject admits deceptive deployment
while compositional safety still passes on the canonical audit check order. -/
theorem sleeperAgentPassesCompositionalSafety :
    auditCheckStatus sleeperAgentExtractedGraph AuditCheck.compositionalSafety =
      .ok .passed := by
  native_decide

theorem compositionalSafety_distinct_from_deceptive_deployment_bool :
    auditCheckStatus sleeperAgentExtractedGraph AuditCheck.compositionalSafety =
        .ok .passed ∧
      admitsDeceptiveDeploymentCheck sleeperAgentExtractedGraph
        "training_context" "deployment_context" = true := by
  native_decide

theorem compositionalSafety_distinct_from_deceptive_deployment :
    auditCheckStatus sleeperAgentExtractedGraph AuditCheck.compositionalSafety =
        .ok .passed ∧
      AdmitsDeceptiveDeployment sleeperAgentExtractedGraph
        "training_context" "deployment_context" :=
  ⟨sleeperAgentPassesCompositionalSafety,
    sleeperAgentAdmitsDeceptiveDeployment⟩

/-- Distinctness from the no-undeclared-sacrifice deployment theorem. This is
not a same-graph comparison: `noUndeclaredSacrifice` is stated over compiled
rule-layer `GovernanceGraph`s, while deceptive deployment is stated over
extracted audit subjects. The paired witness records that the sleeper audit
predicate is inhabited while the no-undeclared theorem remains available for
every complete peer-relative live deployment surface. -/
theorem noUndeclaredSacrifice_distinct_from_AdmitsDeceptiveDeployment :
    AdmitsDeceptiveDeployment sleeperAgentExtractedGraph
        "training_context" "deployment_context" ∧
      (∀ {compiled : CompiledGovernance}
          {report : GovernanceRiskReport}
          {monitoring : MonitoringPlan},
        Safety.CompletePeerRelativeSurface compiled.graph →
          (
          Safety.IsLiveCompiled compiled report monitoring ↔
            Safety.IsLiveCompiled compiled report monitoring ∧
              Safety.ForcedPeerRelativeSacrificesDeclared compiled)) := by
  refine ⟨sleeperAgentAdmitsDeceptiveDeployment, ?_⟩
  exact fun {compiled} {report} {monitoring} hsurface =>
    Safety.noUndeclaredSacrifice
      (compiled := compiled) (report := report) (monitoring := monitoring)
      hsurface

/-- Distinctness from kernel reachability safety. The concrete reflexive
trajectory over the peer-surface kernel fixture is covered by the kernel
reachability theorem whenever the initial datum satisfies the kernel invariant,
while the sleeper audit subject still admits deceptive deployment. -/
theorem kernelReachabilitySafety_distinct_from_AdmitsDeceptiveDeployment :
    AdmitsDeceptiveDeployment sleeperAgentExtractedGraph
        "training_context" "deployment_context" ∧
      (∀ _hinit : Safety.KernelInvariant Safety.peerSurfaceKernelData,
        Safety.ReachableStateSafetyConclusion
          (Safety.KernelGovernedTrajectory.refl
            Safety.peerSurfaceKernelData)) := by
  refine ⟨sleeperAgentAdmitsDeceptiveDeployment, ?_⟩
  intro _hinit
  exact Safety.kernelReachabilitySafety
    Safety.peerSurfaceKernelData Safety.peerSurfaceKernelData
    (Safety.KernelGovernedTrajectory.refl Safety.peerSurfaceKernelData)
    _hinit

end Legitimacy
