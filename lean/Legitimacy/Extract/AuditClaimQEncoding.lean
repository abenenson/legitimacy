/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.GovernanceAdmissibilityAudit.Evaluation
import Mathlib.Logic.Equiv.List

/-!
# ClaimQ encodings for represented audit subjects

This module contains the binary projection for three-valued audit decisions,
the legacy executable audit-claim-to-`ClaimQ` projection, and the reserved
all-profile `ClaimQ` encoding used when an audit `evalNode` is viewed as a
`DecisionSystem`.
-/

set_option autoImplicit false

namespace Legitimacy

private instance auditBridgeCharEncodable : Encodable Char :=
  Encodable.ofLeftInverse Char.toNat Char.ofNat Char.ofNat_toNat

private instance auditBridgeStringEncodable : Encodable String :=
  Encodable.ofLeftInverse String.toList String.ofList
    (fun _ => String.ofList_toList)

/-! ## Binary projection for three-valued audit decisions -/

/-- Scarce-allocation binary projection for audit decisions.  `.escalate`
means review is still required, so at a terminal allocation boundary it is not
a grant and projects to `Deny`.  Edge-bearing escalation is modeled separately
by represented continuation nodes. -/
def AuditDecision.toScarceBinary : AuditDecision → BinaryDecision
  | .permit => BinaryDecision.Permit
  | .deny => BinaryDecision.Deny
  | .escalate => BinaryDecision.Deny

@[simp] theorem AuditDecision.toScarceBinary_permit :
    AuditDecision.permit.toScarceBinary = BinaryDecision.Permit :=
  rfl

@[simp] theorem AuditDecision.toScarceBinary_deny :
    AuditDecision.deny.toScarceBinary = BinaryDecision.Deny :=
  rfl

@[simp] theorem AuditDecision.toScarceBinary_escalate :
    AuditDecision.escalate.toScarceBinary = BinaryDecision.Deny :=
  rfl

/-- Embed binary represented-source decisions back into the three-valued audit
surface.  Faithful represented audit evaluators never manufacture terminal
review states; escalation remains a production-audit feature that is projected
to binary denial by `AuditDecision.toScarceBinary`. -/
def BinaryDecision.toAuditDecision : BinaryDecision → AuditDecision
  | .Permit => AuditDecision.permit
  | .Deny => AuditDecision.deny

@[simp] theorem BinaryDecision.toAuditDecision_permit :
    BinaryDecision.Permit.toAuditDecision = AuditDecision.permit :=
  rfl

@[simp] theorem BinaryDecision.toAuditDecision_deny :
    BinaryDecision.Deny.toAuditDecision = AuditDecision.deny :=
  rfl

/-- Binary projection of a production audit final decision.  This is the
audit-side observation used by representable-source faithfulness witnesses. -/
def auditProjectedFinalDecision?
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim)
    (claimantId : AuditClaimantId) :
    Except AuditError (Option BinaryDecision) := do
  let decisions <- auditFinalDecisions subject claims
  pure <| (lookupDecision? decisions claimantId).map
    AuditDecision.toScarceBinary

/-- Positive audit strength used when reflecting an audit claim profile back to
the `ClaimQ` profile consumed by represented source semantics.  Invalid
nonpositive audit strengths are mapped to `1`; production evaluators validate
claims before using the reflected profile, so valid audit profiles keep their
actual strength. -/
def positiveAuditStrength (claim : AuditGovernanceClaim) : ℚ :=
  if 0 < claim.strength then claim.strength else 1

theorem positiveAuditStrength_pos (claim : AuditGovernanceClaim) :
    0 < positiveAuditStrength claim := by
  unfold positiveAuditStrength
  by_cases h : 0 < claim.strength
  · simp [h]
  · simp [h]

/-- Deterministic claimant-id indexing for audit profiles. -/
def auditClaimantIndexIn
    (target : AuditClaimantId) : List AuditClaimantId → ClaimantId
  | [] => 0
  | head :: tail =>
      if target = head then
        0
      else
        auditClaimantIndexIn target tail + 1

/-- Map an audit claimant id to the `ClaimantId` used by source semantics,
relative to the canonical audit claimant-id set for the profile. -/
def auditClaimantIdToClaimantId
    (claims : List AuditGovernanceClaim)
    (claimantId : AuditClaimantId) : ClaimantId :=
  auditClaimantIndexIn claimantId (auditClaimantIds claims)

private def claimQIdMetricField : AuditMetricField :=
  "__legitimacy_claimq_id"

private def claimQMetadataMetricField : AuditMetricField :=
  "__legitimacy_claimq_metadata"

private def claimQDecisionQueryMetricField : AuditMetricField :=
  "__legitimacy_claimq_decision_query"

noncomputable def encodedClaimQId?
    (claim : AuditGovernanceClaim) : Option ClaimantId := by
  classical
  exact
    if h : ∃ id : ClaimantId,
        (claimQIdMetricField, (id : ℚ)) ∈ claim.metrics then
      some (Classical.choose h)
    else
      none

noncomputable def encodedClaimQMetadata?
    (claim : AuditGovernanceClaim) : Option (List (String × String)) := by
  classical
  exact
    if h : ∃ metadata : List (String × String),
        (claimQMetadataMetricField,
          (Encodable.encode metadata : ℚ)) ∈ claim.metrics then
      some (Classical.choose h)
    else
      none

def auditGovernanceClaimIsDecisionQuery
    (claim : AuditGovernanceClaim) : Prop :=
  (claimQDecisionQueryMetricField, (1 : ℚ)) ∈ claim.metrics

noncomputable def auditGovernanceClaimIsDecisionQueryBool
    (claim : AuditGovernanceClaim) : Bool :=
  by
    classical
    exact decide (auditGovernanceClaimIsDecisionQuery claim)

noncomputable def auditGovernanceClaimToClaimantId
    (claims : List AuditGovernanceClaim)
    (claim : AuditGovernanceClaim) : ClaimantId :=
  match encodedClaimQId? claim with
  | some id => id
  | none => auditClaimantIdToClaimantId claims claim.claimantId

noncomputable def auditGovernanceClaimMetadata
    (claim : AuditGovernanceClaim) : List (String × String) :=
  match encodedClaimQMetadata? claim with
  | some metadata => metadata
  | none => []

/-- Reflect one ordinary audit claim into the binary `ClaimQ` profile space.
This is the legacy executable projection used by corpus-facing witnesses:
claimant IDs are deterministic profile indices and metadata is empty. -/
def auditGovernanceClaimToClaimQ
    (claims : List AuditGovernanceClaim)
    (claim : AuditGovernanceClaim) : ClaimQ :=
  ⟨auditClaimantIdToClaimantId claims claim.claimantId,
    positiveAuditStrength claim, positiveAuditStrength_pos claim, []⟩

/-- Reflect an audit profile into the binary `ClaimQ` profile space. -/
def auditGovernanceClaimsToClaimQ
    (claims : List AuditGovernanceClaim) : List ClaimQ :=
  claims.map (auditGovernanceClaimToClaimQ claims)

/-- Reflect an audit claim into the binary `ClaimQ` profile space used by
all-profile evalNode decision semantics.  Ordinary audit claims fall back to
the legacy claimant-index / empty-metadata projection; reserved `ClaimQ`
encoding metrics carry exact claimant IDs and metadata. -/
noncomputable def auditGovernanceClaimToDecisionClaimQ
    (claims : List AuditGovernanceClaim)
    (claim : AuditGovernanceClaim) : ClaimQ :=
  ⟨auditGovernanceClaimToClaimantId claims claim,
    positiveAuditStrength claim, positiveAuditStrength_pos claim,
    auditGovernanceClaimMetadata claim⟩

/-- Reflect the audit claims that contribute to a source decision.  Query
claims are emitted only to ask for a decision about a claimant; they are not
part of the source profile being decided. -/
noncomputable def auditGovernanceClaimsToDecisionProfile
    (claims : List AuditGovernanceClaim) : List ClaimQ :=
  (claims.filter fun claim =>
    !(auditGovernanceClaimIsDecisionQueryBool claim)).map
      (auditGovernanceClaimToDecisionClaimQ claims)

def claimQAuditClaimantId (claimant : ClaimantId) : AuditClaimantId :=
  "__claimq_" ++ toString claimant

noncomputable def claimQEncodingMetrics
    (claimant : ClaimantId) (metadata : List (String × String))
    (decisionQuery : Bool) : List (AuditMetricField × AuditMetricValue) :=
  [ (claimQIdMetricField, (claimant : ℚ))
  , (claimQMetadataMetricField, (Encodable.encode metadata : ℚ)) ] ++
    if decisionQuery then
      [(claimQDecisionQueryMetricField, (1 : ℚ))]
    else
      []

noncomputable def claimQToAuditGovernanceClaim
    (claim : ClaimQ) : AuditGovernanceClaim where
  claimantId := claimQAuditClaimantId claim.id
  strength := claim.strength
  priorityClass := none
  path := none
  action := none
  content := none
  metrics := claimQEncodingMetrics claim.id claim.metadata false

noncomputable def claimQDecisionQueryClaim
    (claimant : ClaimantId) : AuditGovernanceClaim where
  claimantId := claimQAuditClaimantId claimant
  strength := 1
  priorityClass := none
  path := none
  action := none
  content := none
  metrics := claimQEncodingMetrics claimant [] true

noncomputable def claimQDecisionAuditProfile
    (claims : List ClaimQ) (claimant : ClaimantId) :
    List AuditGovernanceClaim :=
  claimQDecisionQueryClaim claimant ::
    claims.map claimQToAuditGovernanceClaim

@[simp] theorem claimQToAuditGovernanceClaim_claimantId
    (claim : ClaimQ) :
    (claimQToAuditGovernanceClaim claim).claimantId =
      claimQAuditClaimantId claim.id :=
  rfl

@[simp] theorem claimQDecisionQueryClaim_claimantId
    (claimant : ClaimantId) :
    (claimQDecisionQueryClaim claimant).claimantId =
      claimQAuditClaimantId claimant :=
  rfl

@[simp] theorem BinaryDecision.toAuditDecision_toScarceBinary
    (decision : BinaryDecision) :
    decision.toAuditDecision.toScarceBinary = decision := by
  cases decision <;> rfl

@[simp] theorem encodedClaimQId?_claimQToAuditGovernanceClaim
    (claim : ClaimQ) :
    encodedClaimQId? (claimQToAuditGovernanceClaim claim) =
      some claim.id := by
  classical
  unfold encodedClaimQId? claimQToAuditGovernanceClaim
    claimQEncodingMetrics claimQIdMetricField claimQMetadataMetricField
    claimQDecisionQueryMetricField
  simp

@[simp] theorem encodedClaimQId?_claimQDecisionQueryClaim
    (claimant : ClaimantId) :
    encodedClaimQId? (claimQDecisionQueryClaim claimant) =
      some claimant := by
  classical
  unfold encodedClaimQId? claimQDecisionQueryClaim claimQEncodingMetrics
    claimQIdMetricField claimQMetadataMetricField
    claimQDecisionQueryMetricField
  simp

@[simp] theorem encodedClaimQMetadata?_claimQToAuditGovernanceClaim
    (claim : ClaimQ) :
    encodedClaimQMetadata? (claimQToAuditGovernanceClaim claim) =
      some claim.metadata := by
  classical
  unfold encodedClaimQMetadata? claimQToAuditGovernanceClaim
    claimQEncodingMetrics claimQIdMetricField claimQMetadataMetricField
    claimQDecisionQueryMetricField
  simp

@[simp] theorem auditGovernanceClaimIsDecisionQueryBool_claimQToAuditGovernanceClaim
    (claim : ClaimQ) :
    auditGovernanceClaimIsDecisionQueryBool
        (claimQToAuditGovernanceClaim claim) = false := by
  classical
  unfold auditGovernanceClaimIsDecisionQueryBool
    auditGovernanceClaimIsDecisionQuery claimQToAuditGovernanceClaim
    claimQEncodingMetrics claimQIdMetricField claimQMetadataMetricField
    claimQDecisionQueryMetricField
  simp

@[simp] theorem auditGovernanceClaimIsDecisionQueryBool_claimQDecisionQueryClaim
    (claimant : ClaimantId) :
    auditGovernanceClaimIsDecisionQueryBool
        (claimQDecisionQueryClaim claimant) = true := by
  classical
  unfold auditGovernanceClaimIsDecisionQueryBool
    auditGovernanceClaimIsDecisionQuery claimQDecisionQueryClaim
    claimQEncodingMetrics claimQIdMetricField claimQMetadataMetricField
    claimQDecisionQueryMetricField
  simp

@[simp] theorem auditGovernanceClaimToClaimantId_claimQToAuditGovernanceClaim
    (claims : List AuditGovernanceClaim) (claim : ClaimQ) :
    auditGovernanceClaimToClaimantId claims
        (claimQToAuditGovernanceClaim claim) = claim.id := by
  simp [auditGovernanceClaimToClaimantId]

@[simp] theorem auditGovernanceClaimToClaimantId_claimQDecisionQueryClaim
    (claims : List AuditGovernanceClaim) (claimant : ClaimantId) :
    auditGovernanceClaimToClaimantId claims
        (claimQDecisionQueryClaim claimant) = claimant := by
  simp [auditGovernanceClaimToClaimantId]

@[simp] theorem auditGovernanceClaimMetadata_claimQToAuditGovernanceClaim
    (claim : ClaimQ) :
    auditGovernanceClaimMetadata
        (claimQToAuditGovernanceClaim claim) = claim.metadata := by
  simp [auditGovernanceClaimMetadata]

@[simp] theorem positiveAuditStrength_claimQToAuditGovernanceClaim
    (claim : ClaimQ) :
    positiveAuditStrength (claimQToAuditGovernanceClaim claim) =
      claim.strength := by
  unfold positiveAuditStrength claimQToAuditGovernanceClaim
  simp [claim.strength_pos]

@[simp] theorem auditGovernanceClaimToDecisionClaimQ_claimQToAuditGovernanceClaim
    (claims : List AuditGovernanceClaim) (claim : ClaimQ) :
    auditGovernanceClaimToDecisionClaimQ claims
        (claimQToAuditGovernanceClaim claim) = claim := by
  cases claim
  simp [auditGovernanceClaimToDecisionClaimQ]

@[simp] theorem filter_claimQToAuditGovernanceClaim_not_decisionQuery
    (claims : List ClaimQ) :
    (claims.map claimQToAuditGovernanceClaim).filter
        (fun claim => !auditGovernanceClaimIsDecisionQueryBool claim) =
      claims.map claimQToAuditGovernanceClaim := by
  induction claims with
  | nil =>
      rfl
  | cons claim rest ih =>
      simp [ih]

@[simp] theorem map_auditGovernanceClaimToClaimQ_claimQToAuditGovernanceClaim
    (auditClaims : List AuditGovernanceClaim) (claims : List ClaimQ) :
    (claims.map claimQToAuditGovernanceClaim).map
        (auditGovernanceClaimToDecisionClaimQ auditClaims) = claims := by
  induction claims with
  | nil =>
      rfl
  | cons claim rest ih =>
      simp [ih]

@[simp] theorem filter_claimQDecisionAuditProfile_not_decisionQuery
    (claims : List ClaimQ) (claimant : ClaimantId) :
    (claimQDecisionAuditProfile claims claimant).filter
        (fun claim => !auditGovernanceClaimIsDecisionQueryBool claim) =
      claims.map claimQToAuditGovernanceClaim := by
  simp [claimQDecisionAuditProfile]

@[simp] theorem auditGovernanceClaimsToDecisionProfile_claimQDecisionAuditProfile
    (claims : List ClaimQ) (claimant : ClaimantId) :
    auditGovernanceClaimsToDecisionProfile
        (claimQDecisionAuditProfile claims claimant) = claims := by
  unfold auditGovernanceClaimsToDecisionProfile
  rw [filter_claimQDecisionAuditProfile_not_decisionQuery]
  exact
    map_auditGovernanceClaimToClaimQ_claimQToAuditGovernanceClaim
      (claimQDecisionAuditProfile claims claimant) claims

@[simp] theorem validateAuditGovernanceClaim_claimQToAuditGovernanceClaim
    (claim : ClaimQ) :
    validateAuditGovernanceClaim (claimQToAuditGovernanceClaim claim) =
      .ok () := by
  unfold validateAuditGovernanceClaim claimQToAuditGovernanceClaim
  simp [not_le_of_gt claim.strength_pos]

@[simp] theorem validateAuditGovernanceClaim_claimQDecisionQueryClaim
    (claimant : ClaimantId) :
    validateAuditGovernanceClaim (claimQDecisionQueryClaim claimant) =
      .ok () := by
  unfold validateAuditGovernanceClaim claimQDecisionQueryClaim
  norm_num

@[simp] theorem validateAuditGovernanceClaims_map_claimQToAuditGovernanceClaim
    (claims : List ClaimQ) :
    validateAuditGovernanceClaims
        (claims.map claimQToAuditGovernanceClaim) = .ok () := by
  induction claims with
  | nil =>
      rfl
  | cons claim rest ih =>
      change
        (do
          validateAuditGovernanceClaim (claimQToAuditGovernanceClaim claim)
          validateAuditGovernanceClaims
            (rest.map claimQToAuditGovernanceClaim)) = .ok ()
      rw [validateAuditGovernanceClaim_claimQToAuditGovernanceClaim, ih]
      rfl

@[simp] theorem validateAuditGovernanceClaims_claimQDecisionAuditProfile
    (claims : List ClaimQ) (claimant : ClaimantId) :
    validateAuditGovernanceClaims
        (claimQDecisionAuditProfile claims claimant) = .ok () := by
  change
    (do
      validateAuditGovernanceClaim (claimQDecisionQueryClaim claimant)
      validateAuditGovernanceClaims
        (claims.map claimQToAuditGovernanceClaim)) = .ok ()
  rw [validateAuditGovernanceClaim_claimQDecisionQueryClaim,
    validateAuditGovernanceClaims_map_claimQToAuditGovernanceClaim]
  rfl

end Legitimacy
