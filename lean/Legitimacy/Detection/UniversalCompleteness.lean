/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.CaseStudies.UniversalRepair
import Mathlib.Tactic.Linarith

/-! # Universal Detection Completeness

Probe result for the four graph-diagnostic failure kinds used by
`UniversalRepair`.

The detector currently exposed by the substrate is propositional:
`AxiomFailureKind.detected failure graph` is definitionally the negation of
the corresponding graph diagnostic. Therefore the existing soundness direction
and the completeness direction coincide at this abstraction level.

This does not assert executable search completeness for a finite witness finder.
It records the exact Prop-level theorem supported by the current substrate.
-/

set_option autoImplicit false

namespace Legitimacy

/-- A real graph-level governance failure for one of the four universal repair
failure kinds. -/
def AxiomFailureKind.realFailure
    (failure : AxiomFailureKind) (graph : GovernanceGraph) : Prop :=
  ¬ failure.satisfies graph

/-- The detector and the semantic failure predicate are definitionally aligned
in the current Prop-level substrate. -/
theorem AxiomFailureKind.detected_iff_realFailure
    (failure : AxiomFailureKind) (graph : GovernanceGraph) :
    failure.detected graph ↔ failure.realFailure graph := by
  rfl

/-- Soundness on a class: every substrate detection corresponds to a real
governance failure. -/
def DetectionSoundOn (C : Set GovernanceGraph) : Prop :=
  ∀ ⦃graph : GovernanceGraph⦄,
    graph ∈ C →
      ∀ failure : AxiomFailureKind,
        failure.detected graph → failure.realFailure graph

/-- Completeness on a class: every real governance failure in the class is
detected by the substrate detector. -/
def DetectionCompleteOn (C : Set GovernanceGraph) : Prop :=
  ∀ ⦃graph : GovernanceGraph⦄,
    graph ∈ C →
      ∀ failure : AxiomFailureKind,
        failure.realFailure graph → failure.detected graph

/-- Every class is sound for the current Prop-level detector. -/
theorem detectionSoundOn_universal (C : Set GovernanceGraph) :
    DetectionSoundOn C := by
  intro graph _hgraph failure hdetected
  exact hdetected

/-- Every class is complete for the current Prop-level detector because
detection is definitionally the corresponding failure predicate. -/
theorem propLevelDetectionCompleteOn_universal_isDefinitional
    (C : Set GovernanceGraph) :
    DetectionCompleteOn C := by
  intro graph _hgraph failure hfailure
  exact hfailure

/-- The class of all governance graphs. This is a non-restrictive class used to
state that the Prop-level completeness result is not limited to a vacuous
subset. -/
def AllGovernanceGraphs : Set GovernanceGraph :=
  Set.univ

/-- Prop-level definitional completeness over all governance graphs. -/
theorem propLevelDetectionCompleteOn_allGovernanceGraphs_isDefinitional :
    DetectionCompleteOn AllGovernanceGraphs :=
  propLevelDetectionCompleteOn_universal_isDefinitional AllGovernanceGraphs

/-- Universal soundness over all governance graphs. -/
theorem detectionSoundOn_allGovernanceGraphs :
    DetectionSoundOn AllGovernanceGraphs :=
  detectionSoundOn_universal AllGovernanceGraphs

/-- The single-node class from the probe brief. -/
def SingleNodeGraphs : Set GovernanceGraph :=
  fun graph => ∃ node : GovernanceNodeFn, graph = [node]

/-- The single-node class is nonempty. -/
theorem singleNodeGraphs_nonempty :
    ∃ graph : GovernanceGraph, graph ∈ SingleNodeGraphs := by
  exact ⟨peerGraph, peerRelativeNode, rfl⟩

/-- The single-node class includes a real monotonicity failure, so this probe is
not using an empty or failure-free class. -/
theorem singleNodeGraphs_failure_bearing :
    ∃ graph : GovernanceGraph,
      graph ∈ SingleNodeGraphs ∧
        AxiomFailureKind.realFailure
          .monotonicity_violation graph := by
  exact
    ⟨peerGraph, ⟨peerRelativeNode, rfl⟩, peerGraph_not_monotone⟩

/-- Completeness for the candidate single-node class. -/
theorem detectionCompleteOn_singleNodeGraphs :
    DetectionCompleteOn SingleNodeGraphs :=
  propLevelDetectionCompleteOn_universal_isDefinitional SingleNodeGraphs

/-- The profile-blind class from the probe brief, formalized by the existing
claimant-constant predicate. -/
def ProfileBlindGraphs : Set GovernanceGraph :=
  fun graph => ClaimantConstant graph

/-- The profile-blind class is nonempty. -/
theorem profileBlindGraphs_nonempty :
    ∃ graph : GovernanceGraph, graph ∈ ProfileBlindGraphs := by
  refine ⟨claimantConstGraph (fun _ => BinaryDecision.Permit), ?_⟩
  exact
    ⟨fun _ => BinaryDecision.Permit, by
      intro claims claimant _hmem _hdist
      simp [claimantConstGraph, graphDecide]⟩

/-- Completeness for the candidate profile-blind class. -/
theorem detectionCompleteOn_profileBlindGraphs :
    DetectionCompleteOn ProfileBlindGraphs :=
  propLevelDetectionCompleteOn_universal_isDefinitional ProfileBlindGraphs

/-- The all-graphs class is failure-bearing: `peerGraph` is inside it and has a
real monotonicity failure. -/
theorem allGovernanceGraphs_failure_bearing :
    ∃ graph : GovernanceGraph,
      graph ∈ AllGovernanceGraphs ∧
        AxiomFailureKind.realFailure
          .monotonicity_violation graph := by
  exact ⟨peerGraph, by simp [AllGovernanceGraphs], peerGraph_not_monotone⟩

/-!
## Executable representative-profile detector

The detector below is intentionally Boolean and structural: it evaluates the
graph on fixed finite witness profiles and transformed profiles. It does not
call `AxiomFailureKind.satisfies`, `AxiomFailureKind.detected`, or
`AxiomFailureKind.realFailure`.
-/

def detectorScaleClaims (α : ℚ) (hα : 0 < α) (claims : List ClaimQ) :
    List ClaimQ :=
  claims.map
    (fun c => ⟨c.id, α * c.strength, mul_pos hα c.strength_pos, c.metadata⟩)

def consistencyWitnessPresent
    (graph : GovernanceGraph) (claims : List ClaimQ)
    (denied survivor : ClaimantId) : Bool :=
  (graphDecide graph claims denied == BinaryDecision.Deny) &&
    (graphDecide graph claims survivor == BinaryDecision.Permit) &&
      (graphDecide graph (removeClaimGraph denied claims) survivor ==
        BinaryDecision.Deny)

def solidarityWitnessPresent
    (graph : GovernanceGraph) (claims : List ClaimQ)
    (α : ℚ) (hα : 0 < α) (claimant : ClaimantId) : Bool :=
  graphDecide graph claims claimant !=
    graphDecide graph (detectorScaleClaims α hα claims) claimant

def monotonicityWitnessPresent
    (graph : GovernanceGraph) (claims : List ClaimQ)
    (strengthened : ClaimantId) (newStrength : ℚ)
    (hnewStrength : 0 < newStrength) (affected : ClaimantId) : Bool :=
  (graphDecide graph claims affected == BinaryDecision.Permit) &&
    (graphDecide graph
      (strengthenClaim strengthened newStrength hnewStrength claims)
      affected == BinaryDecision.Deny)

def strategyproofnessWitnessPresent
    (graph : GovernanceGraph) (claims : List ClaimQ)
    (claimant : ClaimantId) (reportedStrength : ℚ)
    (hreportedStrength : 0 < reportedStrength) : Bool :=
  (graphDecide graph claims claimant == BinaryDecision.Deny) &&
    (graphDecide graph
      (strengthenClaim claimant reportedStrength hreportedStrength claims)
      claimant == BinaryDecision.Permit)

def detectorConsistencyA : ClaimQ := ⟨0, 1 / 4, by norm_num, []⟩
def detectorConsistencyB : ClaimQ := ⟨1, 1 / 2, by norm_num, []⟩
def detectorConsistencyC : ClaimQ := ⟨2, 3 / 4, by norm_num, []⟩
def detectorConsistencyD : ClaimQ := ⟨3, 1, by norm_num, []⟩

def detectorConsistencyClaims : List ClaimQ :=
  [detectorConsistencyA, detectorConsistencyB,
    detectorConsistencyC, detectorConsistencyD]

def detectorSolidarityA : ClaimQ := ⟨0, 1 / 4, by norm_num, []⟩
def detectorSolidarityB : ClaimQ := ⟨1, 1 / 4, by norm_num, []⟩
def detectorSolidarityC : ClaimQ := ⟨2, 1 / 4, by norm_num, []⟩

def detectorSolidarityClaims : List ClaimQ :=
  [detectorSolidarityA, detectorSolidarityB, detectorSolidarityC]

def detectorMonotonicityA : ClaimQ := ⟨0, 1 / 4, by norm_num, []⟩
def detectorMonotonicityB : ClaimQ := ⟨1, 1 / 2, by norm_num, []⟩
def detectorMonotonicityC : ClaimQ := ⟨2, 3 / 4, by norm_num, []⟩

def detectorMonotonicityClaims : List ClaimQ :=
  [detectorMonotonicityA, detectorMonotonicityB,
    detectorMonotonicityC]

def detectorStrategyproofnessA : ClaimQ := ⟨0, 3 / 4, by norm_num, []⟩
def detectorStrategyproofnessB : ClaimQ := ⟨1, 1 / 2, by norm_num, []⟩
def detectorStrategyproofnessC : ClaimQ := ⟨2, 1 / 4, by norm_num, []⟩

def detectorStrategyproofnessClaims : List ClaimQ :=
  [detectorStrategyproofnessA, detectorStrategyproofnessB,
    detectorStrategyproofnessC]

def enumerativeDetector
    (graph : GovernanceGraph) : AxiomFailureKind → Bool
  | .consistency_violation =>
      consistencyWitnessPresent graph detectorConsistencyClaims 0 1
  | .solidarity_violation =>
      solidarityWitnessPresent graph detectorSolidarityClaims
        2 (by norm_num) 1
  | .monotonicity_violation =>
      monotonicityWitnessPresent graph detectorMonotonicityClaims
        0 (3 / 4) (by norm_num) 1
  | .strategyproofness_bridge_violation =>
      strategyproofnessWitnessPresent graph
        detectorStrategyproofnessClaims 2 (3 / 4) (by norm_num)

/-- A finite-profile version of the executable witness detector. Its
consistency branch searches only the supplied finite set of
`(claims, denied, survivor)` profiles. The remaining branches reuse simple
finite-profile interpretations of the same triples. -/
def enumerativeDetectorWithProfile
    (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId))
    (graph : GovernanceGraph) : AxiomFailureKind → Prop
  | .consistency_violation =>
      ∃ profile ∈ profileSet,
        consistencyWitnessPresent graph profile.1 profile.2.1
          profile.2.2 = true
  | .solidarity_violation =>
      ∃ profile ∈ profileSet,
        solidarityWitnessPresent graph profile.1
          2 (by norm_num) profile.2.1 = true
  | .monotonicity_violation =>
      ∃ profile ∈ profileSet,
        monotonicityWitnessPresent graph profile.1 profile.2.1
          (3 / 4) (by norm_num) profile.2.2 = true
  | .strategyproofness_bridge_violation =>
      ∃ profile ∈ profileSet,
        strategyproofnessWitnessPresent graph profile.1 profile.2.1
          (3 / 4) (by norm_num) = true

def detectorProfileMaxId
    (profile : List ClaimQ × ClaimantId × ClaimantId) : ClaimantId :=
  max profile.2.1 profile.2.2

def profileSetFreshId
    (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    ClaimantId :=
  profileSet.sup detectorProfileMaxId + 1

theorem profile_first_lt_fresh
    {profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)}
    {profile : List ClaimQ × ClaimantId × ClaimantId}
    (hprofile : profile ∈ profileSet) :
    profile.2.1 < profileSetFreshId profileSet := by
  unfold profileSetFreshId detectorProfileMaxId
  exact
    Nat.lt_succ_of_le
      ((Nat.le_max_left profile.2.1 profile.2.2).trans
        (Finset.le_sup (f := detectorProfileMaxId) hprofile))

theorem profile_second_lt_fresh
    {profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)}
    {profile : List ClaimQ × ClaimantId × ClaimantId}
    (hprofile : profile ∈ profileSet) :
    profile.2.2 < profileSetFreshId profileSet := by
  unfold profileSetFreshId detectorProfileMaxId
  exact Nat.lt_succ_of_le ((Nat.le_max_right profile.2.1 profile.2.2).trans
    (Finset.le_sup (f := detectorProfileMaxId) hprofile))

def profileDodgeConsistencyA
    (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    ClaimQ :=
  ⟨profileSetFreshId profileSet, 1 / 3, by norm_num, []⟩

def profileDodgeConsistencyB
    (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    ClaimQ :=
  ⟨profileSetFreshId profileSet + 1, 2 / 3, by norm_num, []⟩

def profileDodgeConsistencyClaims
    (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    List ClaimQ :=
  [profileDodgeConsistencyA profileSet,
    profileDodgeConsistencyB profileSet]

def profileDodgeConsistencyNode
    (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    GovernanceNodeFn :=
  fun claims claimant =>
    if
        claims = profileDodgeConsistencyClaims profileSet ∧
          claimant = profileSetFreshId profileSet then
      BinaryDecision.Deny
    else if
        claims = profileDodgeConsistencyClaims profileSet ∧
          claimant = profileSetFreshId profileSet + 1 then
      BinaryDecision.Permit
    else if
        claims =
            removeClaimGraph (profileSetFreshId profileSet)
              (profileDodgeConsistencyClaims profileSet) ∧
          claimant = profileSetFreshId profileSet + 1 then
      BinaryDecision.Deny
    else
      BinaryDecision.Permit

def profileDodgeConsistencyGraph
    (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    GovernanceGraph :=
  [profileDodgeConsistencyNode profileSet]

theorem profileDodgeConsistencyGraph_singleNode
    (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    profileDodgeConsistencyGraph profileSet ∈ SingleNodeGraphs := by
  exact ⟨profileDodgeConsistencyNode profileSet, rfl⟩

theorem profileDodgeConsistencyClaims_distinct
    (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    ClaimsDistinct (profileDodgeConsistencyClaims profileSet) := by
  unfold ClaimsDistinct profileDodgeConsistencyClaims
    profileDodgeConsistencyA profileDodgeConsistencyB
  simp

theorem profileDodgeConsistencyA_in
    (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    InClaims (profileSetFreshId profileSet)
      (profileDodgeConsistencyClaims profileSet) :=
  ⟨profileDodgeConsistencyA profileSet,
    by simp [profileDodgeConsistencyClaims], rfl⟩

theorem profileDodgeConsistencyB_in
    (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    InClaims (profileSetFreshId profileSet + 1)
      (profileDodgeConsistencyClaims profileSet) :=
  ⟨profileDodgeConsistencyB profileSet,
    by simp [profileDodgeConsistencyClaims], rfl⟩

theorem profileDodgeConsistency_witness
    (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    consistencyWitnessPresent (profileDodgeConsistencyGraph profileSet)
      (profileDodgeConsistencyClaims profileSet)
      (profileSetFreshId profileSet)
      (profileSetFreshId profileSet + 1) = true := by
  unfold consistencyWitnessPresent profileDodgeConsistencyGraph
    profileDodgeConsistencyNode profileDodgeConsistencyClaims
    profileDodgeConsistencyA profileDodgeConsistencyB
  simp [graphDecide, removeClaimGraph]

theorem profileDodgeConsistencyGraph_permits_below_fresh
    {profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)}
    {claims : List ClaimQ} {claimant : ClaimantId}
    (hclaimant : claimant < profileSetFreshId profileSet) :
    graphDecide (profileDodgeConsistencyGraph profileSet) claims claimant =
      BinaryDecision.Permit := by
  have hne_fresh : claimant ≠ profileSetFreshId profileSet :=
    ne_of_lt hclaimant
  have hne_survivor : claimant ≠ profileSetFreshId profileSet + 1 :=
    ne_of_lt (hclaimant.trans (Nat.lt_succ_self _))
  simp [profileDodgeConsistencyGraph, profileDodgeConsistencyNode,
    graphDecide, hne_fresh, hne_survivor]

theorem profileDodgeConsistency_detector_misses
    (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    ¬ enumerativeDetectorWithProfile profileSet
      (profileDodgeConsistencyGraph profileSet)
      .consistency_violation := by
  intro hdetected
  rcases hdetected with ⟨profile, hprofile, hwitness⟩
  have hpermit :
      graphDecide (profileDodgeConsistencyGraph profileSet) profile.1
        profile.2.1 = BinaryDecision.Permit :=
    profileDodgeConsistencyGraph_permits_below_fresh
      (profile_first_lt_fresh hprofile)
  unfold consistencyWitnessPresent at hwitness
  rw [hpermit] at hwitness
  simp at hwitness
def profileDodgeSolidarityA (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) : ClaimQ :=
  ⟨profileSetFreshId profileSet, 1 / 4, by norm_num, []⟩
def profileDodgeSolidarityClaims (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) : List ClaimQ :=
  [profileDodgeSolidarityA profileSet]
def profileDodgeSolidarityNode (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) : GovernanceNodeFn := fun claims claimant =>
  if claims = profileDodgeSolidarityClaims profileSet ∧ claimant = profileSetFreshId profileSet then BinaryDecision.Deny
  else if claims = detectorScaleClaims 2 (by norm_num) (profileDodgeSolidarityClaims profileSet) ∧ claimant = profileSetFreshId profileSet then BinaryDecision.Permit
  else BinaryDecision.Permit
def profileDodgeSolidarityGraph (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) : GovernanceGraph :=
  [profileDodgeSolidarityNode profileSet]
def profileDodgeSolidarity_witnessHits (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) (profile : List ClaimQ × ClaimantId × ClaimantId) : Prop :=
  solidarityWitnessPresent (profileDodgeSolidarityGraph profileSet) profile.1 2 (by norm_num) profile.2.1 = true
theorem profileDodgeSolidarityGraph_singleNode (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    profileDodgeSolidarityGraph profileSet ∈ SingleNodeGraphs := by
  exact ⟨profileDodgeSolidarityNode profileSet, rfl⟩
theorem profileDodgeSolidarityA_in (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    InClaims (profileSetFreshId profileSet) (profileDodgeSolidarityClaims profileSet) :=
  ⟨profileDodgeSolidarityA profileSet, by simp [profileDodgeSolidarityClaims], rfl⟩
theorem profileDodgeSolidarity_witness (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    solidarityWitnessPresent (profileDodgeSolidarityGraph profileSet) (profileDodgeSolidarityClaims profileSet) 2 (by norm_num) (profileSetFreshId profileSet) = true := by
  unfold solidarityWitnessPresent profileDodgeSolidarityGraph
    profileDodgeSolidarityNode profileDodgeSolidarityClaims
    profileDodgeSolidarityA detectorScaleClaims
  simp [graphDecide]
theorem profileDodgeSolidarityGraph_permits_below_fresh {profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)} {claims : List ClaimQ} {claimant : ClaimantId}
    (hclaimant : claimant < profileSetFreshId profileSet) :
    graphDecide (profileDodgeSolidarityGraph profileSet) claims claimant = BinaryDecision.Permit := by
  have hne_fresh : claimant ≠ profileSetFreshId profileSet := ne_of_lt hclaimant
  simp [profileDodgeSolidarityGraph, profileDodgeSolidarityNode, graphDecide, hne_fresh]
theorem profileDodgeSolidarity_detector_misses (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    ∀ profile ∈ profileSet, ¬ profileDodgeSolidarity_witnessHits profileSet profile := by
  intro profile hprofile hwitness
  have hpermit :
      graphDecide (profileDodgeSolidarityGraph profileSet) profile.1
        profile.2.1 = BinaryDecision.Permit :=
    profileDodgeSolidarityGraph_permits_below_fresh (profile_first_lt_fresh hprofile)
  have hpermit_scaled :
      graphDecide (profileDodgeSolidarityGraph profileSet)
        (detectorScaleClaims 2 (by norm_num) profile.1) profile.2.1 =
          BinaryDecision.Permit :=
    profileDodgeSolidarityGraph_permits_below_fresh (profile_first_lt_fresh hprofile)
  unfold profileDodgeSolidarity_witnessHits solidarityWitnessPresent at hwitness
  rw [hpermit, hpermit_scaled] at hwitness
  simp at hwitness
def profileDodgeMonotonicityA (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) : ClaimQ :=
  ⟨profileSetFreshId profileSet, 1 / 4, by norm_num, []⟩
def profileDodgeMonotonicityB (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) : ClaimQ :=
  ⟨profileSetFreshId profileSet + 1, 1 / 2, by norm_num, []⟩
def profileDodgeMonotonicityClaims (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) : List ClaimQ :=
  [profileDodgeMonotonicityA profileSet, profileDodgeMonotonicityB profileSet]
def profileDodgeMonotonicityNode (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) : GovernanceNodeFn := fun claims claimant =>
  if claims = strengthenClaim (profileSetFreshId profileSet) (3 / 4) (by norm_num) (profileDodgeMonotonicityClaims profileSet) ∧ claimant = profileSetFreshId profileSet + 1 then BinaryDecision.Deny
  else BinaryDecision.Permit
def profileDodgeMonotonicityGraph (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) : GovernanceGraph :=
  [profileDodgeMonotonicityNode profileSet]
def profileDodgeMonotonicity_witnessHits (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) (profile : List ClaimQ × ClaimantId × ClaimantId) : Prop :=
  monotonicityWitnessPresent (profileDodgeMonotonicityGraph profileSet) profile.1 profile.2.1 (3 / 4) (by norm_num) profile.2.2 = true
theorem profileDodgeMonotonicityGraph_singleNode (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    profileDodgeMonotonicityGraph profileSet ∈ SingleNodeGraphs := by
  exact ⟨profileDodgeMonotonicityNode profileSet, rfl⟩
theorem profileDodgeMonotonicityClaims_distinct (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    ClaimsDistinct (profileDodgeMonotonicityClaims profileSet) := by
  unfold ClaimsDistinct profileDodgeMonotonicityClaims
    profileDodgeMonotonicityA profileDodgeMonotonicityB
  simp
theorem profileDodgeMonotonicityA_in (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    InClaims (profileSetFreshId profileSet) (profileDodgeMonotonicityClaims profileSet) :=
  ⟨profileDodgeMonotonicityA profileSet, by simp [profileDodgeMonotonicityClaims], rfl⟩
theorem profileDodgeMonotonicity_strength_le (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    ∀ c ∈ profileDodgeMonotonicityClaims profileSet, c.id = profileSetFreshId profileSet → c.strength ≤ (3 : ℚ) / 4 := by
  intro c hm hid
  simp [profileDodgeMonotonicityClaims] at hm
  rcases hm with rfl | rfl
  · simp [profileDodgeMonotonicityA]; norm_num
  · simp [profileDodgeMonotonicityB] at hid
theorem profileDodgeMonotonicity_witness (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    monotonicityWitnessPresent (profileDodgeMonotonicityGraph profileSet) (profileDodgeMonotonicityClaims profileSet) (profileSetFreshId profileSet) (3 / 4) (by norm_num) (profileSetFreshId profileSet + 1) = true := by
  unfold monotonicityWitnessPresent profileDodgeMonotonicityGraph
    profileDodgeMonotonicityNode profileDodgeMonotonicityClaims
    profileDodgeMonotonicityA profileDodgeMonotonicityB
  norm_num [graphDecide, strengthenClaim]
theorem profileDodgeMonotonicityGraph_permits_below_fresh {profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)} {claims : List ClaimQ} {claimant : ClaimantId}
    (hclaimant : claimant < profileSetFreshId profileSet) :
    graphDecide (profileDodgeMonotonicityGraph profileSet) claims claimant = BinaryDecision.Permit := by
  have hne_survivor : claimant ≠ profileSetFreshId profileSet + 1 := ne_of_lt (hclaimant.trans (Nat.lt_succ_self _))
  simp [profileDodgeMonotonicityGraph, profileDodgeMonotonicityNode, graphDecide, hne_survivor]
theorem profileDodgeMonotonicity_detector_misses (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    ∀ profile ∈ profileSet, ¬ profileDodgeMonotonicity_witnessHits profileSet profile := by
  intro profile hprofile hwitness
  have hpermit_strengthened :
      graphDecide (profileDodgeMonotonicityGraph profileSet)
        (strengthenClaim profile.2.1 (3 / 4) (by norm_num) profile.1)
        profile.2.2 = BinaryDecision.Permit :=
    profileDodgeMonotonicityGraph_permits_below_fresh (profile_second_lt_fresh hprofile)
  unfold profileDodgeMonotonicity_witnessHits monotonicityWitnessPresent at hwitness
  rw [hpermit_strengthened] at hwitness
  simp at hwitness
def profileDodgeStrategyproofnessA (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) : ClaimQ :=
  ⟨profileSetFreshId profileSet, 1 / 4, by norm_num, []⟩
def profileDodgeStrategyproofnessClaims (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) : List ClaimQ :=
  [profileDodgeStrategyproofnessA profileSet]
def profileDodgeStrategyproofnessNode (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) : GovernanceNodeFn := fun claims claimant =>
  if claims = profileDodgeStrategyproofnessClaims profileSet ∧ claimant = profileSetFreshId profileSet then BinaryDecision.Deny
  else BinaryDecision.Permit
def profileDodgeStrategyproofnessGraph (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) : GovernanceGraph :=
  [profileDodgeStrategyproofnessNode profileSet]
def profileDodgeStrategyproofness_witnessHits (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) (profile : List ClaimQ × ClaimantId × ClaimantId) : Prop :=
  strategyproofnessWitnessPresent (profileDodgeStrategyproofnessGraph profileSet) profile.1 profile.2.1 (3 / 4) (by norm_num) = true
theorem profileDodgeStrategyproofnessGraph_singleNode (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    profileDodgeStrategyproofnessGraph profileSet ∈ SingleNodeGraphs := by
  exact ⟨profileDodgeStrategyproofnessNode profileSet, rfl⟩
theorem profileDodgeStrategyproofnessClaims_distinct (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    ClaimsDistinct (profileDodgeStrategyproofnessClaims profileSet) := by
  unfold ClaimsDistinct profileDodgeStrategyproofnessClaims profileDodgeStrategyproofnessA
  simp
theorem profileDodgeStrategyproofnessA_in (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    InClaims (profileSetFreshId profileSet) (profileDodgeStrategyproofnessClaims profileSet) :=
  ⟨profileDodgeStrategyproofnessA profileSet, by simp [profileDodgeStrategyproofnessClaims], rfl⟩
theorem profileDodgeStrategyproofness_witness (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    strategyproofnessWitnessPresent (profileDodgeStrategyproofnessGraph profileSet) (profileDodgeStrategyproofnessClaims profileSet) (profileSetFreshId profileSet) (3 / 4) (by norm_num) = true := by
  unfold strategyproofnessWitnessPresent profileDodgeStrategyproofnessGraph
    profileDodgeStrategyproofnessNode profileDodgeStrategyproofnessClaims
    profileDodgeStrategyproofnessA
  norm_num [graphDecide, strengthenClaim]
theorem profileDodgeStrategyproofnessGraph_permits_below_fresh {profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)} {claims : List ClaimQ} {claimant : ClaimantId}
    (hclaimant : claimant < profileSetFreshId profileSet) :
    graphDecide (profileDodgeStrategyproofnessGraph profileSet) claims claimant = BinaryDecision.Permit := by
  have hne_fresh : claimant ≠ profileSetFreshId profileSet := ne_of_lt hclaimant
  simp [profileDodgeStrategyproofnessGraph, profileDodgeStrategyproofnessNode, graphDecide, hne_fresh]
theorem profileDodgeStrategyproofness_detector_misses (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    ∀ profile ∈ profileSet, ¬ profileDodgeStrategyproofness_witnessHits profileSet profile := by
  intro profile hprofile hwitness
  have hpermit :
      graphDecide (profileDodgeStrategyproofnessGraph profileSet) profile.1
        profile.2.1 = BinaryDecision.Permit :=
    profileDodgeStrategyproofnessGraph_permits_below_fresh (profile_first_lt_fresh hprofile)
  unfold profileDodgeStrategyproofness_witnessHits strategyproofnessWitnessPresent at hwitness
  rw [hpermit] at hwitness
  simp at hwitness

/-- The structural class on which the representative detector is complete:
the canonical single-stage peer-relative graph. -/
def CanonicalPeerRelativeGraphs : Set GovernanceGraph :=
  fun graph => graph = peerGraph

theorem canonicalPeerRelativeGraphs_nonempty :
    ∃ graph : GovernanceGraph, graph ∈ CanonicalPeerRelativeGraphs := by
  exact ⟨peerGraph, rfl⟩

theorem canonicalPeerRelativeGraphs_failure_bearing :
    ∃ graph : GovernanceGraph,
      graph ∈ CanonicalPeerRelativeGraphs ∧
        AxiomFailureKind.realFailure
          .monotonicity_violation graph := by
  exact ⟨peerGraph, rfl, peerGraph_not_monotone⟩

theorem detectorConsistencyClaims_distinct :
    ClaimsDistinct detectorConsistencyClaims := by
  unfold ClaimsDistinct detectorConsistencyClaims detectorConsistencyA
    detectorConsistencyB detectorConsistencyC detectorConsistencyD
  decide

theorem detectorConsistencyA_in :
    InClaims 0 detectorConsistencyClaims :=
  ⟨detectorConsistencyA, by simp [detectorConsistencyClaims], rfl⟩

theorem detectorConsistencyB_in :
    InClaims 1 detectorConsistencyClaims :=
  ⟨detectorConsistencyB, by simp [detectorConsistencyClaims], rfl⟩

theorem detectorSolidarityB_in :
    InClaims 1 detectorSolidarityClaims :=
  ⟨detectorSolidarityB, by simp [detectorSolidarityClaims], rfl⟩

theorem detectorMonotonicityClaims_distinct :
    ClaimsDistinct detectorMonotonicityClaims := by
  unfold ClaimsDistinct detectorMonotonicityClaims detectorMonotonicityA
    detectorMonotonicityB detectorMonotonicityC
  decide

theorem detectorMonotonicityA_in :
    InClaims 0 detectorMonotonicityClaims :=
  ⟨detectorMonotonicityA, by simp [detectorMonotonicityClaims], rfl⟩

theorem detectorMonotonicity_strength_le :
    ∀ c ∈ detectorMonotonicityClaims,
      c.id = 0 → c.strength ≤ (3 : ℚ) / 4 := by
  intro c hm hid
  simp [detectorMonotonicityClaims] at hm
  rcases hm with rfl | rfl | rfl
  · simp [detectorMonotonicityA]
    norm_num
  · simp [detectorMonotonicityB] at hid
  · simp [detectorMonotonicityC] at hid

theorem detectorStrategyproofnessClaims_distinct :
    ClaimsDistinct detectorStrategyproofnessClaims := by
  unfold ClaimsDistinct detectorStrategyproofnessClaims
    detectorStrategyproofnessA detectorStrategyproofnessB
    detectorStrategyproofnessC
  decide

theorem detectorStrategyproofnessC_in :
    InClaims 2 detectorStrategyproofnessClaims :=
  ⟨detectorStrategyproofnessC,
    by simp [detectorStrategyproofnessClaims], rfl⟩

theorem consistencyWitnessPresent_sound
    (graph : GovernanceGraph) (claims : List ClaimQ)
    (denied survivor : ClaimantId)
    (hne : denied ≠ survivor)
    (hdenied : InClaims denied claims)
    (hsurvivor : InClaims survivor claims)
    (hdistinct : ClaimsDistinct claims)
    (hwitness :
      consistencyWitnessPresent graph claims denied survivor = true) :
    ¬ GraphConsistency graph := by
  intro hconsistent
  unfold consistencyWitnessPresent at hwitness
  rcases Bool.and_eq_true_iff.mp hwitness with ⟨hinitial, hremovedBool⟩
  rcases Bool.and_eq_true_iff.mp hinitial with ⟨hdenyBool, hpermitBool⟩
  have hdeny :
      graphDecide graph claims denied = BinaryDecision.Deny := by
    simpa using hdenyBool
  have hpermit :
      graphDecide graph claims survivor = BinaryDecision.Permit := by
    simpa using hpermitBool
  have hremoved :
      graphDecide graph (removeClaimGraph denied claims) survivor =
        BinaryDecision.Deny := by
    simpa using hremovedBool
  have hsame :=
    hconsistent claims denied survivor
      hdenied hsurvivor hne hdistinct hdeny
  rw [hpermit, hremoved] at hsame
  cases hsame

theorem profileDodgeConsistency_realFailure
    (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    AxiomFailureKind.realFailure .consistency_violation
      (profileDodgeConsistencyGraph profileSet) := by
  exact
    consistencyWitnessPresent_sound
      (profileDodgeConsistencyGraph profileSet)
      (profileDodgeConsistencyClaims profileSet)
      (profileSetFreshId profileSet)
      (profileSetFreshId profileSet + 1)
      (ne_of_lt (Nat.lt_succ_self _))
      (profileDodgeConsistencyA_in profileSet)
      (profileDodgeConsistencyB_in profileSet)
      (profileDodgeConsistencyClaims_distinct profileSet)
      (profileDodgeConsistency_witness profileSet)

theorem solidarityWitnessPresent_sound
    (graph : GovernanceGraph) (claims : List ClaimQ)
    (α : ℚ) (hα : 1 ≤ α) (claimant : ClaimantId)
    (hclaimant : InClaims claimant claims)
    (hwitness :
      solidarityWitnessPresent graph claims α
        (lt_of_lt_of_le zero_lt_one hα) claimant = true) :
    ¬ GraphSolidarity graph := by
  intro hsolid
  have hdifferent :
      graphDecide graph claims claimant ≠
        graphDecide graph
          (detectorScaleClaims α (lt_of_lt_of_le zero_lt_one hα) claims)
          claimant := by
    simpa [solidarityWitnessPresent] using hwitness
  exact hdifferent (hsolid claims α (lt_of_lt_of_le zero_lt_one hα)
    claimant hclaimant)
theorem profileDodgeSolidarity_realFailure (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    AxiomFailureKind.realFailure .solidarity_violation (profileDodgeSolidarityGraph profileSet) := by
  exact solidarityWitnessPresent_sound (profileDodgeSolidarityGraph profileSet) (profileDodgeSolidarityClaims profileSet)
    2 (by norm_num) (profileSetFreshId profileSet) (profileDodgeSolidarityA_in profileSet) (profileDodgeSolidarity_witness profileSet)

theorem monotonicityWitnessPresent_sound
    (graph : GovernanceGraph) (claims : List ClaimQ)
    (strengthened affected : ClaimantId)
    (newStrength : ℚ) (hnewStrength : 0 < newStrength)
    (hstrengthened : InClaims strengthened claims)
    (hdistinct : ClaimsDistinct claims)
    (hbound :
      ∀ c ∈ claims, c.id = strengthened → c.strength ≤ newStrength)
    (hwitness :
      monotonicityWitnessPresent graph claims strengthened
        newStrength hnewStrength affected = true) :
    ¬ GraphMonotonicity graph := by
  intro hmonotone
  unfold monotonicityWitnessPresent at hwitness
  rcases Bool.and_eq_true_iff.mp hwitness with ⟨hpermitBool, hdenyBool⟩
  have hpermit :
      graphDecide graph claims affected = BinaryDecision.Permit := by
    simpa using hpermitBool
  have hdeny :
      graphDecide graph
        (strengthenClaim strengthened newStrength hnewStrength claims)
        affected = BinaryDecision.Deny := by
    simpa using hdenyBool
  have hpermit' :=
    hmonotone claims strengthened newStrength hnewStrength affected
      hstrengthened hdistinct hbound hpermit
  rw [hdeny] at hpermit'
  cases hpermit'
theorem profileDodgeMonotonicity_realFailure (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    AxiomFailureKind.realFailure .monotonicity_violation (profileDodgeMonotonicityGraph profileSet) := by
  exact monotonicityWitnessPresent_sound (profileDodgeMonotonicityGraph profileSet) (profileDodgeMonotonicityClaims profileSet)
    (profileSetFreshId profileSet) (profileSetFreshId profileSet + 1) (3 / 4) (by norm_num)
    (profileDodgeMonotonicityA_in profileSet) (profileDodgeMonotonicityClaims_distinct profileSet)
    (profileDodgeMonotonicity_strength_le profileSet) (profileDodgeMonotonicity_witness profileSet)

theorem strategyproofnessWitnessPresent_sound
    (graph : GovernanceGraph) (claims : List ClaimQ)
    (claimant : ClaimantId) (reportedStrength : ℚ)
    (hreportedStrength : 0 < reportedStrength)
    (hclaimant : InClaims claimant claims)
    (hdistinct : ClaimsDistinct claims)
    (hwitness :
      strategyproofnessWitnessPresent graph claims claimant
        reportedStrength hreportedStrength = true) :
    ¬ GraphStrategyproofness graph := by
  intro hstrategyproof
  unfold strategyproofnessWitnessPresent at hwitness
  rcases Bool.and_eq_true_iff.mp hwitness with ⟨hdenyBool, hpermitBool⟩
  have hdeny :
      graphDecide graph claims claimant = BinaryDecision.Deny := by
    simpa using hdenyBool
  have hpermit' :
      graphDecide graph
        (strengthenClaim claimant reportedStrength hreportedStrength claims)
        claimant = BinaryDecision.Permit := by
    simpa using hpermitBool
  have hpermit :=
    hstrategyproof claims claimant reportedStrength hreportedStrength
      hclaimant hdistinct hpermit'
  rw [hdeny] at hpermit
  cases hpermit
theorem profileDodgeStrategyproofness_realFailure (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    AxiomFailureKind.realFailure .strategyproofness_bridge_violation (profileDodgeStrategyproofnessGraph profileSet) := by
  exact strategyproofnessWitnessPresent_sound (profileDodgeStrategyproofnessGraph profileSet) (profileDodgeStrategyproofnessClaims profileSet)
    (profileSetFreshId profileSet) (3 / 4) (by norm_num) (profileDodgeStrategyproofnessA_in profileSet)
    (profileDodgeStrategyproofnessClaims_distinct profileSet) (profileDodgeStrategyproofness_witness profileSet)

theorem lookupStrength_detectorScaleClaims
    (claims : List ClaimQ) (k : ClaimantId) (α : ℚ) (hα : 0 < α) :
    lookupStrength k (detectorScaleClaims α hα claims) =
      α * lookupStrength k claims := by
  induction claims with
  | nil =>
      simp [detectorScaleClaims, lookupStrength]
  | cons c cs ih =>
      by_cases hk : c.id = k
      · simp [detectorScaleClaims, lookupStrength, hk]
      · simpa [detectorScaleClaims, lookupStrength, hk] using ih

theorem countAtMost_detectorScaleClaims
    (claims : List ClaimQ) (α : ℚ) (hα : 0 < α) (s : ℚ) :
    countAtMost (detectorScaleClaims α hα claims) (α * s) =
      countAtMost claims s := by
  induction claims with
  | nil =>
      simp [countAtMost, detectorScaleClaims]
  | cons c cs ih =>
      by_cases hcs : c.strength ≤ s
      · have hscaled : α * c.strength ≤ α * s := by
          nlinarith
        simpa [countAtMost, detectorScaleClaims, hcs, hscaled] using ih
      · have hscaled : ¬ α * c.strength ≤ α * s := by
          intro h
          apply hcs
          nlinarith
        simpa [countAtMost, detectorScaleClaims, hcs, hscaled] using ih

theorem peerGraph_solidary_for_enumerativeDetector :
    GraphSolidarity peerGraph := by
  intro claims α hα j hj
  change
    graphDecide peerGraph claims j =
      graphDecide peerGraph (detectorScaleClaims α hα claims) j
  have hlookup :
      lookupStrength j (detectorScaleClaims α hα claims) =
        α * lookupStrength j claims := by
    simpa using lookupStrength_detectorScaleClaims claims j α hα
  have hcount :
      countAtMost (detectorScaleClaims α hα claims)
          (α * lookupStrength j claims) =
        countAtMost claims (lookupStrength j claims) := by
    simpa using
      countAtMost_detectorScaleClaims claims α hα
        (lookupStrength j claims)
  rw [show graphDecide peerGraph claims j =
      if 2 * countAtMost claims (lookupStrength j claims) ≥ claims.length then
        BinaryDecision.Permit else BinaryDecision.Deny by
        simp [peerGraph, graphDecide, peerRelativeNode]
        split_ifs <;> rfl,
    show graphDecide peerGraph (detectorScaleClaims α hα claims) j =
      if
          2 *
              countAtMost (detectorScaleClaims α hα claims)
                (lookupStrength j
                  (detectorScaleClaims α hα claims)) ≥
            (detectorScaleClaims α hα claims).length then
        BinaryDecision.Permit else BinaryDecision.Deny by
        simp [peerGraph, graphDecide, peerRelativeNode]
        split_ifs <;> rfl]
  rw [hlookup, hcount]
  simp [detectorScaleClaims]

theorem enumerativeDetector_peerGraph_consistency :
    enumerativeDetector peerGraph
      .consistency_violation = true := by
  native_decide

theorem enumerativeDetector_peerGraph_solidarity :
    enumerativeDetector peerGraph
      .solidarity_violation = false := by
  native_decide

theorem enumerativeDetector_peerGraph_monotonicity :
    enumerativeDetector peerGraph
      .monotonicity_violation = true := by
  native_decide

theorem enumerativeDetector_peerGraph_strategyproofness :
    enumerativeDetector peerGraph
      .strategyproofness_bridge_violation = true := by
  native_decide

/-- A single-node graph whose consistency failure is away from the detector's
representative consistency profile. -/
def singleNodeConsistencyCounterexampleA : ClaimQ :=
  ⟨10, 1 / 3, by norm_num, []⟩

def singleNodeConsistencyCounterexampleB : ClaimQ :=
  ⟨11, 2 / 3, by norm_num, []⟩

def singleNodeConsistencyCounterexampleClaims : List ClaimQ :=
  [singleNodeConsistencyCounterexampleA,
    singleNodeConsistencyCounterexampleB]

def singleNodeConsistencyCounterexampleNode : GovernanceNodeFn :=
  fun claims claimant =>
    if claims = singleNodeConsistencyCounterexampleClaims ∧ claimant = 10 then
      BinaryDecision.Deny
    else if
        claims = singleNodeConsistencyCounterexampleClaims ∧
          claimant = 11 then
      BinaryDecision.Permit
    else if
        claims =
            removeClaimGraph 10 singleNodeConsistencyCounterexampleClaims ∧
          claimant = 11 then
      BinaryDecision.Deny
    else
      BinaryDecision.Permit

def singleNodeConsistencyCounterexampleGraph : GovernanceGraph :=
  [singleNodeConsistencyCounterexampleNode]

theorem singleNodeConsistencyCounterexampleGraph_singleNode :
    singleNodeConsistencyCounterexampleGraph ∈ SingleNodeGraphs := by
  exact ⟨singleNodeConsistencyCounterexampleNode, rfl⟩

theorem singleNodeConsistencyCounterexampleClaims_distinct :
    ClaimsDistinct singleNodeConsistencyCounterexampleClaims := by
  unfold ClaimsDistinct singleNodeConsistencyCounterexampleClaims
    singleNodeConsistencyCounterexampleA singleNodeConsistencyCounterexampleB
  decide

theorem singleNodeConsistencyCounterexampleA_in :
    InClaims 10 singleNodeConsistencyCounterexampleClaims :=
  ⟨singleNodeConsistencyCounterexampleA,
    by simp [singleNodeConsistencyCounterexampleClaims], rfl⟩

theorem singleNodeConsistencyCounterexampleB_in :
    InClaims 11 singleNodeConsistencyCounterexampleClaims :=
  ⟨singleNodeConsistencyCounterexampleB,
    by simp [singleNodeConsistencyCounterexampleClaims], rfl⟩

theorem singleNodeConsistencyCounterexample_witness :
    consistencyWitnessPresent singleNodeConsistencyCounterexampleGraph
      singleNodeConsistencyCounterexampleClaims 10 11 = true := by
  native_decide

theorem singleNodeConsistencyCounterexample_realFailure :
    AxiomFailureKind.realFailure .consistency_violation
      singleNodeConsistencyCounterexampleGraph := by
  exact
    consistencyWitnessPresent_sound
      singleNodeConsistencyCounterexampleGraph
      singleNodeConsistencyCounterexampleClaims
      10 11 (by decide)
      singleNodeConsistencyCounterexampleA_in
      singleNodeConsistencyCounterexampleB_in
      singleNodeConsistencyCounterexampleClaims_distinct
      singleNodeConsistencyCounterexample_witness

theorem singleNodeConsistencyCounterexample_detector_misses :
    enumerativeDetector singleNodeConsistencyCounterexampleGraph
      .consistency_violation = false := by
  native_decide

/-- The representative-profile detector is not complete on all single-node
graphs: arbitrary single-node decision functions can place a violation outside
the fixed representative profile checked by `enumerativeDetector`. -/
theorem enumerativeDetector_not_complete_on_SingleNodeGraphs :
    ∃ graph ∈ SingleNodeGraphs,
      AxiomFailureKind.realFailure .consistency_violation graph ∧
        enumerativeDetector graph .consistency_violation = false := by
  exact
    ⟨singleNodeConsistencyCounterexampleGraph,
      singleNodeConsistencyCounterexampleGraph_singleNode,
      singleNodeConsistencyCounterexample_realFailure,
      singleNodeConsistencyCounterexample_detector_misses⟩

/-- No finite set of witness profiles is complete on all single-node graphs:
a single-node decision function can always place a real consistency violation
at fresh claimant IDs outside the finite profiled search surface. -/
theorem no_finite_profile_detector_complete_on_SingleNodeGraphs :
    ∀ (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)),
      ∃ G ∈ SingleNodeGraphs, ∃ failure : AxiomFailureKind,
        failure.realFailure G ∧
        ¬ enumerativeDetectorWithProfile profileSet G failure := by
  intro profileSet
  exact
    ⟨profileDodgeConsistencyGraph profileSet,
      profileDodgeConsistencyGraph_singleNode profileSet,
      .consistency_violation,
      profileDodgeConsistency_realFailure profileSet,
      profileDodgeConsistency_detector_misses profileSet⟩
theorem profileDodgeSolidarity_detector_misses_all (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    ¬ enumerativeDetectorWithProfile profileSet (profileDodgeSolidarityGraph profileSet) .solidarity_violation := by
  intro hdetected
  rcases hdetected with ⟨profile, hprofile, hwitness⟩
  exact profileDodgeSolidarity_detector_misses profileSet profile hprofile hwitness
theorem profileDodgeMonotonicity_detector_misses_all (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    ¬ enumerativeDetectorWithProfile profileSet (profileDodgeMonotonicityGraph profileSet) .monotonicity_violation := by
  intro hdetected
  rcases hdetected with ⟨profile, hprofile, hwitness⟩
  exact profileDodgeMonotonicity_detector_misses profileSet profile hprofile hwitness
theorem profileDodgeStrategyproofness_detector_misses_all (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)) :
    ¬ enumerativeDetectorWithProfile profileSet (profileDodgeStrategyproofnessGraph profileSet) .strategyproofness_bridge_violation := by
  intro hdetected
  rcases hdetected with ⟨profile, hprofile, hwitness⟩
  exact profileDodgeStrategyproofness_detector_misses profileSet profile hprofile hwitness

/-- No finite set of profiled witness probes is complete for any fixed
failure kind on all single-node graphs. Each branch places the real witness at
fresh claimant IDs outside the finite profiled search surface for that kind. -/
theorem no_finite_profile_detector_complete_per_kind :
    ∀ (kind : AxiomFailureKind) (profileSet : Finset (List ClaimQ × ClaimantId × ClaimantId)),
      ∃ G ∈ SingleNodeGraphs, kind.realFailure G ∧ ¬ enumerativeDetectorWithProfile profileSet G kind := by
  intro kind profileSet
  cases kind
  · exact ⟨profileDodgeConsistencyGraph profileSet, profileDodgeConsistencyGraph_singleNode profileSet,
      profileDodgeConsistency_realFailure profileSet, profileDodgeConsistency_detector_misses profileSet⟩
  · exact ⟨profileDodgeSolidarityGraph profileSet, profileDodgeSolidarityGraph_singleNode profileSet,
      profileDodgeSolidarity_realFailure profileSet, profileDodgeSolidarity_detector_misses_all profileSet⟩
  · exact ⟨profileDodgeMonotonicityGraph profileSet, profileDodgeMonotonicityGraph_singleNode profileSet,
      profileDodgeMonotonicity_realFailure profileSet, profileDodgeMonotonicity_detector_misses_all profileSet⟩
  · exact ⟨profileDodgeStrategyproofnessGraph profileSet, profileDodgeStrategyproofnessGraph_singleNode profileSet,
      profileDodgeStrategyproofness_realFailure profileSet, profileDodgeStrategyproofness_detector_misses_all profileSet⟩

theorem enumerativeDetector_sound_complete_on_canonicalPeerRelativeGraphs :
    ∀ graph ∈ CanonicalPeerRelativeGraphs,
      ∀ failure : AxiomFailureKind,
        enumerativeDetector graph failure = true ↔
          failure.realFailure graph := by
  intro graph hgraph failure
  subst graph
  cases failure
  · constructor
    · intro hdetector
      exact
        consistencyWitnessPresent_sound peerGraph detectorConsistencyClaims
          0 1 (by decide) detectorConsistencyA_in detectorConsistencyB_in
          detectorConsistencyClaims_distinct
          (by simpa [enumerativeDetector] using hdetector)
    · intro _hfailure
      exact enumerativeDetector_peerGraph_consistency
  · constructor
    · intro hdetector
      exact
        solidarityWitnessPresent_sound peerGraph detectorSolidarityClaims
          2 (by norm_num) 1 detectorSolidarityB_in
          (by simpa [enumerativeDetector] using hdetector)
    · intro hfailure
      exact False.elim
        (hfailure peerGraph_solidary_for_enumerativeDetector)
  · constructor
    · intro hdetector
      exact
        monotonicityWitnessPresent_sound peerGraph
          detectorMonotonicityClaims 0 1 (3 / 4) (by norm_num)
          detectorMonotonicityA_in detectorMonotonicityClaims_distinct
          detectorMonotonicity_strength_le
          (by simpa [enumerativeDetector] using hdetector)
    · intro _hfailure
      exact enumerativeDetector_peerGraph_monotonicity
  · constructor
    · intro hdetector
      exact
        strategyproofnessWitnessPresent_sound peerGraph
          detectorStrategyproofnessClaims 2 (3 / 4) (by norm_num)
          detectorStrategyproofnessC_in
          detectorStrategyproofnessClaims_distinct
          (by simpa [enumerativeDetector] using hdetector)
    · intro _hfailure
      exact enumerativeDetector_peerGraph_strategyproofness

end Legitimacy
