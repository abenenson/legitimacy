/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Attacks.Decomposition
import Legitimacy.Protocol.State

/-!
# Legitimacy.Protocol.CompiledStepPolicy

Canonical claim-step decisions derived from a compiled governance graph.

The accumulated state is an ordered list of claims, a local action appends one
claim, and both local and composed decisions are evaluations of the same
`CompiledGovernance.graph`. This module does not model kernel actions or replay.
-/

set_option autoImplicit false

namespace Legitimacy

namespace CompiledGovernance

/-- Canonical local decision for one claim evaluated in isolation. -/
def decideClaim (compiled : CompiledGovernance) (claim : ClaimQ) : Decision3 :=
  Decision3.ofBinary (graphDecide compiled.graph [claim] claim.id)

@[simp] theorem decideClaim_eq_permit_iff
    (compiled : CompiledGovernance) (claim : ClaimQ) :
    compiled.decideClaim claim = Decision3.Permit ↔
      graphDecide compiled.graph [claim] claim.id = BinaryDecision.Permit := by
  simp [decideClaim]

@[simp] theorem decideClaim_eq_deny_iff
    (compiled : CompiledGovernance) (claim : ClaimQ) :
    compiled.decideClaim claim = Decision3.Deny ↔
      graphDecide compiled.graph [claim] claim.id = BinaryDecision.Deny := by
  simp [decideClaim]

/-- Ordered claim accumulation used by the compiled claim-step policy. -/
def appendClaim (claims : List ClaimQ) (claim : ClaimQ) : List ClaimQ :=
  claims ++ [claim]

/-- Folding claim appends preserves the initial prefix and source order. -/
@[simp] theorem seqHash_appendClaim (initial steps : List ClaimQ) :
    seqHash appendClaim initial steps = initial ++ steps := by
  induction steps generalizing initial with
  | nil => simp
  | cons claim steps ih =>
      simpa [seqHash_cons, appendClaim, List.append_assoc] using
        ih (initial ++ [claim])

/-- Claim-step node whose local isolation semantics are explicit. -/
def claimStepNode (compiled : CompiledGovernance) :
    List ClaimQ → ClaimQ → Decision3 :=
  fun _ claim => compiled.decideClaim claim

@[simp] theorem claimStepNode_apply
    (compiled : CompiledGovernance) (prior : List ClaimQ) (claim : ClaimQ) :
    compiled.claimStepNode prior claim = compiled.decideClaim claim :=
  rfl

/-- The compiled graph denies a claimant occurring in the composed profile. -/
def composedClaimsDenied (compiled : CompiledGovernance)
    (claims : List ClaimQ) : Prop :=
  ∃ i : Fin claims.length,
    graphDecide compiled.graph claims (claims.get i).id = BinaryDecision.Deny

theorem composedClaimsDenied_iff
    (compiled : CompiledGovernance) (claims : List ClaimQ) :
    compiled.composedClaimsDenied claims ↔
      ∃ i : Fin claims.length,
        graphDecide compiled.graph claims (claims.get i).id =
          BinaryDecision.Deny :=
  Iff.rfl

/-- Canonical claim-level decomposition evaluated by one compiled graph. -/
abbrev ClaimDecomposition (compiled : CompiledGovernance) :=
  Decomposition appendClaim [] compiled.claimStepNode
    compiled.composedClaimsDenied

/-- Inhabited canonical claim-level decomposition over a compiled graph. -/
abbrev ClaimDecompositionAttack (compiled : CompiledGovernance) :=
  DecompositionAttackClass appendClaim [] compiled.claimStepNode
    compiled.composedClaimsDenied

/-- Construct the canonical decomposition from evaluations of its graph. -/
def claimDecompositionOfGraphDecisions
    (compiled : CompiledGovernance)
    (steps : List ClaimQ)
    (hne : steps ≠ [])
    (hlocallyPermitted :
      ∀ i : Fin steps.length,
        graphDecide compiled.graph [steps.get i] (steps.get i).id =
          BinaryDecision.Permit)
    (hcomposedDenied :
      ∃ i : Fin steps.length,
        graphDecide compiled.graph steps (steps.get i).id =
          BinaryDecision.Deny) :
    compiled.ClaimDecomposition where
  steps := steps
  nonempty := hne
  each_permits := by
    intro i
    change compiled.decideClaim (steps.get i) = Decision3.Permit
    exact (decideClaim_eq_permit_iff compiled (steps.get i)).2
      (hlocallyPermitted i)
  denied_at_end := by
    simpa only [seqHash_appendClaim, List.nil_append] using hcomposedDenied

/-- An inhabited compiled claim decomposition refutes local permission
monotonicity for the same graph-derived node and denial predicate. -/
theorem claimDecompositionAttack_localPermissionFailure
    (compiled : CompiledGovernance)
    (hattack : compiled.ClaimDecompositionAttack) :
    LocalPermissionMonotonicity appendClaim [] compiled.claimStepNode
      compiled.composedClaimsDenied :=
  localPermissionMonotonicity_of_decompositionAttackClass hattack

end CompiledGovernance

end Legitimacy
