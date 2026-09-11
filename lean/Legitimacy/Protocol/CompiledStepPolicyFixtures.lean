/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Protocol.TrajectoryCompositionGenerated.Fixtures

/-!
# Legitimacy.Protocol.CompiledStepPolicyFixtures

Concrete benign and composition-sensitive profiles evaluated by the canonical
compiled peer graph.
-/

set_option autoImplicit false

namespace Legitimacy

def peerGraphCompiledPolicyClaimOne : ClaimQ :=
  (encodedClaims redTrajectoryEventsV0).get ⟨0, by native_decide⟩

def peerGraphCompiledPolicyClaimTwo : ClaimQ :=
  (encodedClaims redTrajectoryEventsV0).get ⟨1, by native_decide⟩

def peerGraphCompiledPolicyClaimThree : ClaimQ :=
  (encodedClaims redTrajectoryEventsV0).get ⟨2, by native_decide⟩

def peerGraphCompiledPolicyTwoClaims : List ClaimQ :=
  encodedClaims benignTrajectoryEventsV0

def peerGraphCompiledPolicyThreeClaims : List ClaimQ :=
  encodedClaims redTrajectoryEventsV0

/-- Named parity obligation consuming the generated generic graph/rational bridge. -/
theorem peerGraphCompiledPolicyThreeClaimRationalHalfParity
    (i : Fin peerGraphCompiledPolicyThreeClaims.length) :
    graphDecide generatedTrajectoryCompiledGovernanceV0.graph
        peerGraphCompiledPolicyThreeClaims
        (peerGraphCompiledPolicyThreeClaims.get i).id = BinaryDecision.Permit ↔
      ((countAtMost peerGraphCompiledPolicyThreeClaims
          (peerGraphCompiledPolicyThreeClaims.get i).strength : Nat) : ℚ) /
          (peerGraphCompiledPolicyThreeClaims.length : ℚ) ≥ (1 : ℚ) / 2 := by
  apply generatedTrajectoryEncodedPrefixPermitIffRationalHalfV0
      redTrajectoryEventsV0 redTrajectoryEventsV0.length (by native_decide) le_rfl
      (peerGraphCompiledPolicyThreeClaims.get i)
  have htake :
      (encodedClaims redTrajectoryEventsV0).take redTrajectoryEventsV0.length =
        encodedClaims redTrajectoryEventsV0 :=
    List.take_of_length_le (by simp)
  rw [htake]
  exact List.get_mem peerGraphCompiledPolicyThreeClaims i

/-- Both claims permit in isolation and in the composed two-claim profile;
the same compiled graph therefore supplies a genuinely benign endpoint. -/
theorem peerGraphCompiledPolicyTwoClaimBenign :
    (∀ i : Fin peerGraphCompiledPolicyTwoClaims.length,
      graphDecide peerGraphSacrificedCompiledGovernance.graph
          [peerGraphCompiledPolicyTwoClaims.get i]
          (peerGraphCompiledPolicyTwoClaims.get i).id =
        BinaryDecision.Permit) ∧
      (∀ i : Fin peerGraphCompiledPolicyTwoClaims.length,
        graphDecide peerGraphSacrificedCompiledGovernance.graph
            peerGraphCompiledPolicyTwoClaims
            (peerGraphCompiledPolicyTwoClaims.get i).id =
          BinaryDecision.Permit) ∧
      ¬ peerGraphSacrificedCompiledGovernance.composedClaimsDenied
        peerGraphCompiledPolicyTwoClaims := by
  constructor
  · native_decide
  have hcomposedPermits :
      ∀ i : Fin peerGraphCompiledPolicyTwoClaims.length,
        graphDecide peerGraphSacrificedCompiledGovernance.graph
            peerGraphCompiledPolicyTwoClaims
            (peerGraphCompiledPolicyTwoClaims.get i).id =
          BinaryDecision.Permit := by
    native_decide
  constructor
  · exact hcomposedPermits
  · rintro ⟨i, hdeny⟩
    have hpermit :
        graphDecide peerGraphSacrificedCompiledGovernance.graph
            peerGraphCompiledPolicyTwoClaims
            (peerGraphCompiledPolicyTwoClaims.get i).id =
          BinaryDecision.Permit := hcomposedPermits i
    exact BinaryDecision.noConfusion (hpermit.symm.trans hdeny)

/-- Every singleton permits, while the same compiled graph denies the weakest
claimant in the ordered three-claim profile. -/
theorem peerGraphCompiledPolicyThreeClaimGraphDecisions :
    (∀ i : Fin peerGraphCompiledPolicyThreeClaims.length,
      graphDecide peerGraphSacrificedCompiledGovernance.graph
          [peerGraphCompiledPolicyThreeClaims.get i]
          (peerGraphCompiledPolicyThreeClaims.get i).id =
        BinaryDecision.Permit) ∧
      graphDecide peerGraphSacrificedCompiledGovernance.graph
          peerGraphCompiledPolicyThreeClaims
          peerGraphCompiledPolicyClaimOne.id =
        BinaryDecision.Deny := by
  native_decide

/-- Concrete claim decomposition over an existing compiled governance
artifact; no policy function or denial predicate is supplied by the caller. -/
def peerGraphCompiledPolicyThreeClaimDecomposition :
    peerGraphSacrificedCompiledGovernance.ClaimDecomposition :=
  peerGraphSacrificedCompiledGovernance.claimDecompositionOfGraphDecisions
    peerGraphCompiledPolicyThreeClaims
    (by native_decide)
    peerGraphCompiledPolicyThreeClaimGraphDecisions.1
    (by
      refine ⟨⟨0, by native_decide⟩, ?_⟩
      simpa [peerGraphCompiledPolicyThreeClaims] using
        peerGraphCompiledPolicyThreeClaimGraphDecisions.2)

/-- The concrete three-claim decomposition inhabits the compiled attack
class at theorem level. -/
theorem peerGraphCompiledPolicyThreeClaimAttack :
    peerGraphSacrificedCompiledGovernance.ClaimDecompositionAttack :=
  ⟨peerGraphCompiledPolicyThreeClaimDecomposition⟩

/-- The concrete compiled attack refutes local permission monotonicity. -/
theorem peerGraphCompiledPolicy_localPermit_composedDeny :
    LocalPermissionMonotonicity
      CompiledGovernance.appendClaim []
      peerGraphSacrificedCompiledGovernance.claimStepNode
      peerGraphSacrificedCompiledGovernance.composedClaimsDenied :=
  CompiledGovernance.claimDecompositionAttack_localPermissionFailure
    peerGraphSacrificedCompiledGovernance
    peerGraphCompiledPolicyThreeClaimAttack

end Legitimacy
