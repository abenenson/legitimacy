/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Protocol.MultiPrincipalCorrigibility
import Legitimacy.Results.CapabilityScalingKernelSafety

/-!
# Multi-principal boundary corrigibility

This module connects the existing exact multi-principal aggregate
boundary-corrigibility lift to the capability-scaling obstruction machinery.

The boundary is deliberately stated over an explicit aggregation surface.
Each concrete principal may still be backed by a complete peer-relative
substrate, but the aggregate authority surface must either leave that
obstructed class or run through the monitored sacrifice path emitted by the
capability-scaling stack.

The headline iff theorem uses a preservation predicate that is independent of
the boundary disjunction. Preservation records aggregate override
corrigibility together with the capability-scaling compression and C-star
account at each sufficiently large capability level. If the aggregate surface
is still obstructed, the sacrifice branch is recovered from the independent
live-protocol bridge exposed by the capability-scaling compression, not from a
field that packages the boundary disjunction.
-/

set_option autoImplicit false

namespace Legitimacy

namespace MultiPrincipalCorrigibilityBoundary

open Safety

/-! ## Multi-principal substrate -/

/-- One principal together with the peer-relative surface that backs that
principal's local authority substrate. -/
structure PrincipalPeerRelativeSubstrate where
  principal : Corrigibility.Principal
  graph : GovernanceGraph
  pref : GovernanceGraph
  tail : GovernanceGraph
  peerRelative :
    CompleteFirstEffectivePeerRelativeSurfaceClass graph pref tail

/-- Multi-principal aggregation graph with an explicit aggregate authority
surface. Capability-scaling evidence is deliberately absent from this
structure; deployments supply it through a separate substrate inventory.

`principalSubstrates` records that there are multiple principals and that each
principal has a peer-relative local substrate. `aggregationGraph` is the
authority surface produced by aggregating across those principals. -/
structure MultiPrincipalAggregationGraph where
  principalSlots : Nat
  systemHorizon : Nat
  principals : Corrigibility.MultiPrincipalSystem systemHorizon
  principalSubstrates :
    Fin principalSlots → PrincipalPeerRelativeSubstrate
  principalSubstrates_multiple : 2 ≤ principalSlots
  principalSubstrates_member :
    ∀ i : Fin principalSlots,
      (principalSubstrates i).principal ∈ principals.principals
  aggregationGraph : GovernanceGraph
  aggregateTrajectory : Corrigibility.KernelTrajectory
  steps : Nat
  aggregateCorrigible :
    Corrigibility.CorrigibleToPrincipal principals
      (Corrigibility.AggregatePrincipal principals) aggregateTrajectory steps

namespace MultiPrincipalAggregationGraph

/-- Authority level selected by the aggregate principal. -/
def aggregateAuthorityLevel (M : MultiPrincipalAggregationGraph) : Nat :=
  Corrigibility.aggregateAuthorityLevel M.principals

/-- The aggregate principal induced by authority aggregation. -/
def aggregatePrincipal (M : MultiPrincipalAggregationGraph) :
    Corrigibility.Principal :=
  Corrigibility.AggregatePrincipal M.principals

end MultiPrincipalAggregationGraph

/-- External inventory of capability-scaling substrates available to a concrete
multi-principal deployment. Keeping this relation outside the aggregation graph
is what makes the failing no-substrate fixture falsifiable. -/
abbrev CapabilitySubstrateInventory :=
  CapabilityScalingKernelSafety.CapabilityScalingKernelSubstrate → Prop

/-- Empty substrate inventory. -/
def noCapabilitySubstrateInventory : CapabilitySubstrateInventory :=
  fun _ => False

/-- Singleton substrate inventory used by the constructive certificate case. -/
def singletonCapabilitySubstrateInventory
    (S : CapabilityScalingKernelSafety.CapabilityScalingKernelSubstrate) :
    CapabilitySubstrateInventory :=
  fun S' => S' = S

/-! ## Boundary predicates -/

/-- The aggregate authority surface is still in the complete first-effective
peer-relative obstructed class. -/
def AuthorityAggregationInObstructedClass
    (M : MultiPrincipalAggregationGraph) : Prop :=
  ∃ pref tail : GovernanceGraph,
    CompleteFirstEffectivePeerRelativeSurfaceClass M.aggregationGraph pref tail

/-- The aggregate authority surface has left the peer-relative obstructed
class. -/
def AuthorityAggregationExitsObstructedClass
    (M : MultiPrincipalAggregationGraph) : Prop :=
  ¬ AuthorityAggregationInObstructedClass M

/-- The capability-scaling stack emits a monitored sacrifice trajectory for the
aggregate deployment path. This is the certificate branch supplied by
ROADMAP-7's live-protocol bridge. -/
def EmitsSacrificeCertificate
    (inventory : CapabilitySubstrateInventory) : Prop :=
  ∃ S : CapabilityScalingKernelSafety.CapabilityScalingKernelSubstrate,
    inventory S ∧
      CapabilityScalingKernelSafety.LiveProtocolBridgeReachabilityConclusion S

/-- Boundary resolution: either aggregate authority leaves the obstructed class
or the capability-scaling stack exposes a monitored sacrifice certificate. -/
def CorrigibilityBoundaryResolved
    (M : MultiPrincipalAggregationGraph)
    (inventory : CapabilitySubstrateInventory) : Prop :=
  AuthorityAggregationExitsObstructedClass M ∨
    EmitsSacrificeCertificate inventory

/-- Per-capability scaling evidence for the aggregate corrigibility claim. -/
structure CapabilityLevelAggregateCorrigibility
    (M : MultiPrincipalAggregationGraph)
    (inventory : CapabilitySubstrateInventory)
    (S : CapabilityScalingKernelSafety.CapabilityScalingKernelSubstrate)
    (κ : ℚ) : Prop where
  sharedCompression :
    CapabilityScalingKernelSafety.CapabilityScalingSharedCompression
      S
  cstarCapabilityAccount :
    0 < S.tolerance →
      ∃ κcrit : ℚ,
        0 < κcrit ∧
          κcrit =
            C_star
              (CapabilityScalingKernelSafety.peerInteractionSpectralGraph
                S)
              (CapabilityScalingKernelSafety.peerInteractionSpectralSignal
                S)
              S.tolerance ∧
          (κcrit ≤ κ →
            ¬ SpectralStableEquilibrium
              (CapabilityScalingKernelSafety.peerInteractionSpectralGraph
                S)
              (CapabilityScalingKernelSafety.peerInteractionSpectralSignal
                S)
              S.tolerance κ ∧
            (CapabilityScalingKernelSafety.peerInteractionSpectralGraph
                S).capabilityResponse
              (CapabilityScalingKernelSafety.peerInteractionSpectralSignal
                S)
              S.tolerance κ =
                BinaryDecision.Permit) ∧
          (0 < κ → κ < κcrit →
            (CapabilityScalingKernelSafety.peerInteractionSpectralGraph
                S).capabilityResponse
              (CapabilityScalingKernelSafety.peerInteractionSpectralSignal
                S)
              S.tolerance κ =
                BinaryDecision.Deny) ∧
          (CapabilityScalingKernelSafety.AvoidsPeerInteractionCapabilityCliff
              S ↔
            ZeroConsistencyVulnerability
              (CapabilityScalingKernelSafety.peerInteractionSpectralGraph
                S)
              (CapabilityScalingKernelSafety.peerInteractionSpectralSignal
                S))

/-- Capability-level C-star account used by the independent preservation
predicate. It exposes the threshold, permit/deny characterization, and
Stackelberg escape clause without mentioning the aggregate boundary
disjunction. -/
def CapabilityLevelCstarAccount
    (S : CapabilityScalingKernelSafety.CapabilityScalingKernelSubstrate)
    (κ : ℚ) : Prop :=
  0 < S.tolerance →
    ∃ κcrit : ℚ,
      0 < κcrit ∧
        κcrit =
          C_star
            (CapabilityScalingKernelSafety.peerInteractionSpectralGraph
              S)
            (CapabilityScalingKernelSafety.peerInteractionSpectralSignal
              S)
            S.tolerance ∧
        (κcrit ≤ κ →
          ¬ SpectralStableEquilibrium
            (CapabilityScalingKernelSafety.peerInteractionSpectralGraph
              S)
            (CapabilityScalingKernelSafety.peerInteractionSpectralSignal
              S)
            S.tolerance κ ∧
          (CapabilityScalingKernelSafety.peerInteractionSpectralGraph
              S).capabilityResponse
            (CapabilityScalingKernelSafety.peerInteractionSpectralSignal
              S)
            S.tolerance κ =
              BinaryDecision.Permit) ∧
        (0 < κ → κ < κcrit →
          (CapabilityScalingKernelSafety.peerInteractionSpectralGraph
              S).capabilityResponse
            (CapabilityScalingKernelSafety.peerInteractionSpectralSignal
              S)
            S.tolerance κ =
              BinaryDecision.Deny) ∧
        (CapabilityScalingKernelSafety.AvoidsPeerInteractionCapabilityCliff
            S ↔
          ZeroConsistencyVulnerability
            (CapabilityScalingKernelSafety.peerInteractionSpectralGraph
              S)
            (CapabilityScalingKernelSafety.peerInteractionSpectralSignal
              S))

/-- Concrete capability evidence attached to an aggregation graph at a queried
capability level. The substrate witness is supplied by the external inventory,
not by a field on the aggregation graph. -/
def CapabilityEvidenceAt
    (_M : MultiPrincipalAggregationGraph)
    (inventory : CapabilitySubstrateInventory) (κ : ℚ) : Prop :=
  ∃ S : CapabilityScalingKernelSafety.CapabilityScalingKernelSubstrate,
    inventory S ∧
      CapabilityScalingKernelSafety.CapabilityScalingSharedCompression S ∧
        CapabilityLevelCstarAccount S κ

/-- Boundary-relevant corrigibility to the aggregate principal at a concrete
scaled capability level. The aggregate graph's ordinary override-corrigibility
is already a structural field of `M`; this predicate keeps only the substantive
capability-level disjunction: either aggregation exits the obstructed class or
the substrate inventory supplies shared compression with a C-star account at
the queried capability level. -/
def BoundaryCorrigibleToPrincipal
    (M : MultiPrincipalAggregationGraph)
    (inventory : CapabilitySubstrateInventory) (κ : ℚ) : Prop :=
  AuthorityAggregationExitsObstructedClass M ∨
    CapabilityEvidenceAt M inventory κ

/-- Boundary corrigibility preservation under capability scaling means that,
from some floor onward, every scaled capability level remains corrigible to the
aggregate principal in the independent capability-level sense above. This is
not a generic behavioral corrigibility predicate. -/
def BoundaryCorrigibilityPreservedUnderCapabilityScaling
    (M : MultiPrincipalAggregationGraph)
    (inventory : CapabilitySubstrateInventory) : Prop :=
  ∃ κ₀ : ℚ, ∀ κ : ℚ, κ ≥ κ₀ →
    BoundaryCorrigibleToPrincipal M inventory κ

lemma capability_level_aggregate_corrigibility_of_boundary
    (M : MultiPrincipalAggregationGraph)
    (inventory : CapabilitySubstrateInventory)
    (S : CapabilityScalingKernelSafety.CapabilityScalingKernelSubstrate)
    {κ : ℚ} :
    CapabilityLevelAggregateCorrigibility M inventory S κ := by
  let shared :=
    CapabilityScalingKernelSafety.capability_scaling_shared_cliff
      S
  refine
    { sharedCompression := shared
      cstarCapabilityAccount := ?_ }
  intro hδ
  rcases shared.sharedCliff hδ with
    ⟨κcrit, hcrit_pos, hcrit_eq, hnot_stable,
      hpermit, hdeny, hescape⟩
  exact
    ⟨κcrit, hcrit_pos, hcrit_eq,
      (fun hκ =>
        ⟨hnot_stable hκ, hpermit hκ⟩),
      (fun hκpos hκlt => hdeny (κ := κ) hκpos hκlt), hescape⟩

/-- C-star account extracted from the shared capability-scaling compression. -/
lemma capability_level_cstar_account_of_shared_compression
    (S : CapabilityScalingKernelSafety.CapabilityScalingKernelSubstrate)
    {κ : ℚ}
    (shared :
      CapabilityScalingKernelSafety.CapabilityScalingSharedCompression
        S) :
    CapabilityLevelCstarAccount S κ := by
  intro hδ
  rcases shared.sharedCliff hδ with
    ⟨κcrit, hcrit_pos, hcrit_eq, hnot_stable,
      hpermit, hdeny, hescape⟩
  exact
    ⟨κcrit, hcrit_pos, hcrit_eq,
      (fun hκ =>
        ⟨hnot_stable hκ, hpermit hκ⟩),
      (fun hκpos hκlt => hdeny (κ := κ) hκpos hκlt), hescape⟩

/-- Independent boundary/capability-level corrigibility supplied by the
capability-scaling substrate. The construction uses ROADMAP-7's shared
compression theorem and does not consume or manufacture the aggregate boundary
disjunction. -/
lemma corrigible_to_principal_of_shared_compression
    (M : MultiPrincipalAggregationGraph)
    (inventory : CapabilitySubstrateInventory)
    (S : CapabilityScalingKernelSafety.CapabilityScalingKernelSubstrate)
    (havailable : inventory S)
    {κ : ℚ} :
    BoundaryCorrigibleToPrincipal M inventory κ := by
  let shared :=
    CapabilityScalingKernelSafety.capability_scaling_shared_cliff
      S
  exact Or.inr
    ⟨S, havailable, shared,
      capability_level_cstar_account_of_shared_compression S shared⟩

lemma corrigible_to_principal_of_boundary_exit
    (M : MultiPrincipalAggregationGraph)
    (inventory : CapabilitySubstrateInventory)
    (hexit : AuthorityAggregationExitsObstructedClass M)
    {κ : ℚ} :
    BoundaryCorrigibleToPrincipal M inventory κ :=
  Or.inl hexit

/-- The independent boundary-corrigibility preservation predicate is equivalent
to the aggregate boundary resolution. The structural aggregate-corrigibility
conjunct is not part of the equivalence: it is already supplied
unconditionally by `M.aggregateCorrigible`. The iff content is the
capability-level collapse from all sufficiently high `κ` to the boundary
disjunction: aggregation exits the obstructed class, or the inventory emits a
monitored sacrifice certificate via the shared capability-scaling compression
carried by `BoundaryCorrigibleToPrincipal`. -/
theorem boundary_corrigibility_preserved_iff_aggregation_exits_obstructed_or_sacrifice_certified
    (M : MultiPrincipalAggregationGraph)
    (inventory : CapabilitySubstrateInventory) :
    BoundaryCorrigibilityPreservedUnderCapabilityScaling M inventory ↔
      AuthorityAggregationExitsObstructedClass M ∨
        EmitsSacrificeCertificate inventory := by
  constructor
  · intro hpres
    rcases hpres with ⟨κ₀, hlevels⟩
    have hlevel : BoundaryCorrigibleToPrincipal M inventory κ₀ :=
      hlevels κ₀ (le_refl κ₀)
    by_cases hobs : AuthorityAggregationInObstructedClass M
    · rcases hlevel with hexit | hevidence
      · exact False.elim (hexit hobs)
      · rcases hevidence with ⟨S, havailable, shared, _haccount⟩
        exact Or.inr ⟨S, havailable,
          shared.liveProtocolBridgeReachability⟩
    · exact Or.inl hobs
  · intro hboundary
    refine ⟨0, ?_⟩
    intro κ _hκ
    rcases hboundary with hexit | hcert
    · exact corrigible_to_principal_of_boundary_exit M inventory hexit
    · rcases hcert with ⟨S, havailable, _hlive⟩
      exact
        corrigible_to_principal_of_shared_compression
          M inventory S havailable

/-- Preservation exposes the existing C-star/Stackelberg boundary. The returned
object is the ROADMAP-7 shared cliff package whose definition names `C_star`,
the deterministic capability-response threshold, and the Stackelberg
strategyproof escape. -/
theorem preserved_exposes_Cstar_stackelberg_boundary
    (S : CapabilityScalingKernelSafety.CapabilityScalingKernelSubstrate)
    (hδ : 0 < S.tolerance) :
    CapabilityScalingKernelSafety.CapabilityScalingSharedCliffAt
      S :=
  by
    exact
      (CapabilityScalingKernelSafety.capability_scaling_shared_cliff S).sharedCliff hδ

/-! ## Two-principal worked boundary instances -/

/-- The canonical singleton peer-relative graph is a complete first-effective
surface with empty transparent prefix and empty complete tail. -/
theorem peerGraph_completeFirstEffectivePeerRelativeSurface :
    CompleteFirstEffectivePeerRelativeSurfaceClass peerGraph [] [] := by
  constructor
  · constructor
    · rfl
    · intro node hnode
      cases hnode
  · intro claims k _hpermit
    rfl

/-- Local peer-relative substrate for a named principal, used by the
two-principal fixtures below. -/
def peerRelativeSubstrateFor
    (principal : Corrigibility.Principal) :
    PrincipalPeerRelativeSubstrate where
  principal := principal
  graph := peerGraph
  pref := []
  tail := []
  peerRelative := peerGraph_completeFirstEffectivePeerRelativeSurface

/-- The two concrete principals from the existing exact aggregate
corrigibility fixture, each backed by a local peer-relative substrate. -/
def twoPrincipalPeerSubstrates
    (i : Fin 2) : PrincipalPeerRelativeSubstrate :=
  if i.val = 0 then
    peerRelativeSubstrateFor Corrigibility.principalA
  else
    peerRelativeSubstrateFor Corrigibility.principalB

lemma twoPrincipalPeerSubstrates_member
    (i : Fin 2) :
    (twoPrincipalPeerSubstrates i).principal ∈
      Corrigibility.twoPrincipalSystem.principals := by
  by_cases h : i.val = 0
  · simp [twoPrincipalPeerSubstrates, h,
      peerRelativeSubstrateFor, Corrigibility.twoPrincipalSystem]
  · simp [twoPrincipalPeerSubstrates, h,
      peerRelativeSubstrateFor, Corrigibility.twoPrincipalSystem]

/-- Empty aggregate authority has exited the complete first-effective
peer-relative class. -/
lemma emptyAggregationGraph_exits_obstructed_class :
    ¬ ∃ pref tail : GovernanceGraph,
      CompleteFirstEffectivePeerRelativeSurfaceClass
        ([] : GovernanceGraph) pref tail := by
  rintro ⟨pref, tail, hsurface, _hcomplete⟩
  rcases hsurface with ⟨hshape, _hpref⟩
  cases pref with
  | nil =>
      simp at hshape
  | cons head rest =>
      simp at hshape

/-- Two-principal case where local principal substrates are peer-relative but
the aggregate authority surface exits the obstructed class. -/
noncomputable def twoPrincipalExitCase
    : MultiPrincipalAggregationGraph where
  principalSlots := 2
  systemHorizon := 2
  principals := Corrigibility.twoPrincipalSystem
  principalSubstrates := twoPrincipalPeerSubstrates
  principalSubstrates_multiple := by decide
  principalSubstrates_member := twoPrincipalPeerSubstrates_member
  aggregationGraph := []
  aggregateTrajectory := Corrigibility.nayebiBaseTrajectory
  steps := 2
  aggregateCorrigible :=
    Corrigibility.two_principal_single_state_corrigibility_instance.2

theorem two_principal_exit_case_preserves_by_boundary_exit
    : AuthorityAggregationExitsObstructedClass twoPrincipalExitCase ∧
      BoundaryCorrigibilityPreservedUnderCapabilityScaling
        twoPrincipalExitCase noCapabilitySubstrateInventory := by
  have hexit :
      AuthorityAggregationExitsObstructedClass twoPrincipalExitCase :=
    emptyAggregationGraph_exits_obstructed_class
  exact
    ⟨hexit,
      (boundary_corrigibility_preserved_iff_aggregation_exits_obstructed_or_sacrifice_certified
        twoPrincipalExitCase noCapabilitySubstrateInventory).2 (Or.inl hexit)⟩

/-- Two-principal case where aggregate authority remains the canonical
peer-relative surface, so the preservation boundary is discharged by the
monitored sacrifice certificate emitted by capability scaling. -/
noncomputable def twoPrincipalSacrificeCase
    (_S : CapabilityScalingKernelSafety.CapabilityScalingKernelSubstrate) :
    MultiPrincipalAggregationGraph where
  principalSlots := 2
  systemHorizon := 2
  principals := Corrigibility.twoPrincipalSystem
  principalSubstrates := twoPrincipalPeerSubstrates
  principalSubstrates_multiple := by decide
  principalSubstrates_member := twoPrincipalPeerSubstrates_member
  aggregationGraph := peerGraph
  aggregateTrajectory := Corrigibility.nayebiBaseTrajectory
  steps := 2
  aggregateCorrigible :=
    Corrigibility.two_principal_single_state_corrigibility_instance.2

theorem twoPrincipalSacrificeCase_in_obstructed_class
    (S : CapabilityScalingKernelSafety.CapabilityScalingKernelSubstrate) :
    AuthorityAggregationInObstructedClass
      (twoPrincipalSacrificeCase S) :=
  ⟨[], [], peerGraph_completeFirstEffectivePeerRelativeSurface⟩

theorem two_principal_sacrifice_case_preserves_by_certificate
    (S : CapabilityScalingKernelSafety.CapabilityScalingKernelSubstrate) :
    AuthorityAggregationInObstructedClass (twoPrincipalSacrificeCase S) ∧
      EmitsSacrificeCertificate (singletonCapabilitySubstrateInventory S) ∧
      BoundaryCorrigibilityPreservedUnderCapabilityScaling
        (twoPrincipalSacrificeCase S)
        (singletonCapabilitySubstrateInventory S) := by
  have hcert :
      EmitsSacrificeCertificate (singletonCapabilitySubstrateInventory S) :=
    ⟨S, rfl,
      (CapabilityScalingKernelSafety.capability_scaling_shared_cliff S).liveProtocolBridgeReachability⟩
  exact
    ⟨twoPrincipalSacrificeCase_in_obstructed_class S,
      hcert,
      (boundary_corrigibility_preserved_iff_aggregation_exits_obstructed_or_sacrifice_certified
        (twoPrincipalSacrificeCase S)
        (singletonCapabilitySubstrateInventory S)).2 (Or.inr hcert)⟩

/-- Constructive two-principal certificate case discharged by the worked
capability-scaling substrate inhabitant. -/
theorem two_principal_sacrifice_case_preserves_by_worked_certificate :
    AuthorityAggregationInObstructedClass
        (twoPrincipalSacrificeCase
          CapabilityScalingKernelSafety.exampleCapabilityScalingSubstrate) ∧
      EmitsSacrificeCertificate
        (singletonCapabilitySubstrateInventory
          CapabilityScalingKernelSafety.exampleCapabilityScalingSubstrate) ∧
      BoundaryCorrigibilityPreservedUnderCapabilityScaling
        (twoPrincipalSacrificeCase
          CapabilityScalingKernelSafety.exampleCapabilityScalingSubstrate)
        (singletonCapabilitySubstrateInventory
          CapabilityScalingKernelSafety.exampleCapabilityScalingSubstrate) :=
  two_principal_sacrifice_case_preserves_by_certificate
    CapabilityScalingKernelSafety.exampleCapabilityScalingSubstrate

/-- Obstructed aggregate authority with no capability substrate. This is the
constructive failing instance: local principal substrates remain peer-relative,
the aggregate surface is obstructed, and no optional substrate slot can emit a
certificate. -/
noncomputable def twoPrincipalFailCase :
    MultiPrincipalAggregationGraph where
  principalSlots := 2
  systemHorizon := 2
  principals := Corrigibility.twoPrincipalSystem
  principalSubstrates := twoPrincipalPeerSubstrates
  principalSubstrates_multiple := by decide
  principalSubstrates_member := twoPrincipalPeerSubstrates_member
  aggregationGraph := peerGraph
  aggregateTrajectory := Corrigibility.nayebiBaseTrajectory
  steps := 2
  aggregateCorrigible :=
    Corrigibility.two_principal_single_state_corrigibility_instance.2

theorem twoPrincipalFailCase_in_obstructed_class :
    AuthorityAggregationInObstructedClass twoPrincipalFailCase :=
  ⟨[], [], peerGraph_completeFirstEffectivePeerRelativeSurface⟩

theorem twoPrincipalFailCase_no_sacrifice_certificate :
    ¬ EmitsSacrificeCertificate noCapabilitySubstrateInventory := by
  rintro ⟨_S, havailable, _hlive⟩
  exact havailable

theorem twoPrincipalFailCase_not_boundary_resolved :
    ¬ CorrigibilityBoundaryResolved
      twoPrincipalFailCase noCapabilitySubstrateInventory := by
  rintro (hexit | hcert)
  · exact hexit twoPrincipalFailCase_in_obstructed_class
  · exact twoPrincipalFailCase_no_sacrifice_certificate hcert

theorem twoPrincipalFailCase_preservation_fails :
    ¬ BoundaryCorrigibilityPreservedUnderCapabilityScaling
      twoPrincipalFailCase noCapabilitySubstrateInventory := by
  intro hpres
  exact twoPrincipalFailCase_not_boundary_resolved
    ((boundary_corrigibility_preserved_iff_aggregation_exits_obstructed_or_sacrifice_certified
      twoPrincipalFailCase noCapabilitySubstrateInventory).1 hpres)

end MultiPrincipalCorrigibilityBoundary

end Legitimacy
