/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/
import Legitimacy.Results.NonPeerRelative
import Legitimacy.CaseStudies.GeneralAdjudicatedRepair
import Legitimacy.Kernel.CompositionalSafety
import Mathlib.Tactic.NormNum
/-! # Universal Repair
This case study separates substantive axiom repair from trivial claimant-constant collapse.
It proves scoped non-collapsed replacements while strict decision-preserving universal repair remains impossible.
The scope is finite graph-diagnostic repair under explicit faithfulness predicates.
-/
set_option autoImplicit false
namespace Legitimacy
inductive AxiomFailureKind where
  | consistency_violation
  | solidarity_violation
  | monotonicity_violation
  | strategyproofness_bridge_violation
  deriving Repr, DecidableEq
def AxiomFailureKind.satisfies : AxiomFailureKind → GovernanceGraph → Prop
  | .consistency_violation, graph => GraphConsistency graph
  | .solidarity_violation, graph => GraphSolidarity graph
  | .monotonicity_violation, graph => GraphMonotonicity graph
  | .strategyproofness_bridge_violation, graph =>
      GraphStrategyproofness graph
def AxiomFailureKind.detected
    (failure : AxiomFailureKind) (graph : GovernanceGraph) : Prop :=
  ¬ failure.satisfies graph
def OtherAxiomPassesPreserved
    (graph repaired : GovernanceGraph) (failure : AxiomFailureKind) :
    Prop :=
  ∀ other : AxiomFailureKind,
    other ≠ failure →
      other.satisfies graph →
        other.satisfies repaired
def ThreePairwiseDistinct (p₁ p₂ p₃ : List ClaimQ × ClaimantId) : Prop := p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃
def ProfileRepairBranchAgreement (graph : GovernanceGraph) (denied permitted : ClaimantId) (p : List ClaimQ × ClaimantId) : Prop :=
  (p.2 = denied ∧ graphDecide graph p.1 p.2 = BinaryDecision.Deny) ∨ (p.2 ≠ denied ∧ p.2 = permitted ∧ graphDecide graph p.1 p.2 = BinaryDecision.Permit) ∨ (p.2 ≠ denied ∧ p.2 ≠ permitted ∧ InClaims p.2 p.1 ∧ graphDecide graph p.1 p.2 = BinaryDecision.Permit) ∨ (p.2 ≠ denied ∧ p.2 ≠ permitted ∧ ¬ InClaims p.2 p.1 ∧ graphDecide graph p.1 p.2 = BinaryDecision.Deny)
instance profileRepairBranchAgreement_decidablePred (graph : GovernanceGraph) (denied permitted : ClaimantId) :
    DecidablePred (ProfileRepairBranchAgreement graph denied permitted) := by intro p; unfold ProfileRepairBranchAgreement; infer_instance
structure NonTrivialRepairFaithfulness
    (graph repaired : GovernanceGraph) : Prop where
  not_behaviorally_collapse :
    ¬ ∃ d : ClaimantId → BinaryDecision,
      ∀ claims claimant, graphDecide repaired claims claimant = d claimant
  preserves_mixed_decision_seed_subset : ∃ S : Set (List ClaimQ × ClaimantId), (∃ p : List ClaimQ × ClaimantId, p ∈ S) ∧ (∀ p : List ClaimQ × ClaimantId, p ∈ S → graphDecide repaired p.1 p.2 = graphDecide graph p.1 p.2) ∧ (∃ p : List ClaimQ × ClaimantId, p ∈ S ∧ graphDecide graph p.1 p.2 = BinaryDecision.Deny) ∧ (∃ p : List ClaimQ × ClaimantId, p ∈ S ∧ graphDecide graph p.1 p.2 = BinaryDecision.Permit)
  preserves_characterizable_subset : ∃ denied permitted : ClaimantId, denied ≠ permitted ∧ ∃ (P : List ClaimQ × ClaimantId → Prop) (_ : DecidablePred P), (∀ p : List ClaimQ × ClaimantId, P p ↔ ProfileRepairBranchAgreement graph denied permitted p) ∧ (∀ p : List ClaimQ × ClaimantId, P p → graphDecide repaired p.1 p.2 = graphDecide graph p.1 p.2) ∧ (∃ p : List ClaimQ × ClaimantId, P p ∧ graphDecide graph p.1 p.2 = BinaryDecision.Deny) ∧ (∃ p : List ClaimQ × ClaimantId, P p ∧ graphDecide graph p.1 p.2 = BinaryDecision.Permit)
  behavioral_non_collapse :
    ∃ (claims : List ClaimQ) (claimant₁ claimant₂ : ClaimantId),
      graphDecide repaired claims claimant₁ ≠
        graphDecide repaired claims claimant₂
  dense_profile_sensitivity :
    ∃ protectedDeny protectedPermit : ClaimantId,
      protectedDeny ≠ protectedPermit ∧
        ∀ outsider : ClaimantId,
          outsider ≠ protectedDeny →
            outsider ≠ protectedPermit →
              ∃ claims₁ claims₂ : List ClaimQ,
                graphDecide repaired claims₁ outsider ≠
                  graphDecide repaired claims₂ outsider
structure SubstantiveRepairWitness
    (graph : GovernanceGraph) (failure : AxiomFailureKind) where
  repaired : GovernanceGraph
  detects_failure : failure.detected graph
  closes_failure : failure.satisfies repaired
  preserves_other_passes :
    OtherAxiomPassesPreserved graph repaired failure
  faithfulness : NonTrivialRepairFaithfulness graph repaired
def SubstantiveRepairExists
    (graph : GovernanceGraph) (failure : AxiomFailureKind) : Prop :=
  ∃ _ : SubstantiveRepairWitness graph failure, True
def nonPeerRelativeCollapse (graph : GovernanceGraph) : GovernanceGraph :=
  claimantConstGraph
    (fun claimant =>
      graph.localDecision claimant 1 (by norm_num))
/-- The non-peer-relative collapse satisfies every legitimacy axiom because it forgets the claim profile and keeps only a claimant-indexed decision table. It is useful as a negative control: axiom satisfaction alone is too weak to rule out a repair that has erased profile-sensitive behavior. -/
theorem nonPeerRelativeCollapse_allLegitimacyAxioms
    (graph : GovernanceGraph) :
    AllLegitimacyAxioms (nonPeerRelativeCollapse graph) := by
  simpa [nonPeerRelativeCollapse] using
    claimantConstGraph_allLegitimacyAxioms
      (fun claimant => graph.localDecision claimant 1 (by norm_num))
/-- Any individual failure kind is satisfied by the non-peer-relative collapse. The proof projects the relevant component from the all-axioms theorem, making the collapse available as a universal but intentionally unfaithful repair candidate. -/
theorem nonPeerRelativeCollapse_satisfies
    (graph : GovernanceGraph) (failure : AxiomFailureKind) :
    failure.satisfies (nonPeerRelativeCollapse graph) := by
  have hall := nonPeerRelativeCollapse_allLegitimacyAxioms graph
  cases failure <;> simp [AxiomFailureKind.satisfies] at hall ⊢
  · exact hall.1
  · exact hall.2.1
  · exact hall.2.2.1
  · exact hall.2.2.2
/-- The non-peer-relative collapse violates the file's nontrivial faithfulness bar. It is behaviorally equivalent to a claimant-only decision function, so it directly contradicts the `not_behaviorally_collapse` field. This theorem is the negative control separating axiom closure from substantive repair. -/
theorem nonPeerRelativeCollapse_not_faithful
    (graph : GovernanceGraph) :
    ¬ NonTrivialRepairFaithfulness graph
      (nonPeerRelativeCollapse graph) := by
  intro hfaith
  apply hfaith.not_behaviorally_collapse
  refine ⟨fun claimant => graph.localDecision claimant 1 (by norm_num), ?_⟩
  intro claims claimant
  simp [nonPeerRelativeCollapse, claimantConstGraph, graphDecide]
  cases graph.localDecision claimant 1 (by norm_num) <;> rfl
theorem emptyGraph_allLegitimacyAxioms :
    AllLegitimacyAxioms ([] : GovernanceGraph) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro claims k j _hk _hj _hkj _hdist hdeny
    simp [graphDecide] at hdeny
  · intro claims α hα j _hj
    simp [graphDecide]
  · intro claims k s' hs' j _hk _hdist _hle _hperm
    simp [graphDecide]
  · intro claims k s_r hs_r _hk _hdist _hperm
    simp [graphDecide]
/-- Every detected axiom failure has some denied decision in the original graph. Otherwise all decisions are permits, from which all four graph axioms can be reconstructed, contradicting the detected failure. This supplies the deny side of the mixed-decision witness used by non-collapsed repair. -/
theorem detected_failure_has_denied_decision
    (graph : GovernanceGraph) (failure : AxiomFailureKind)
    (hdetected : failure.detected graph) :
    ∃ (claims : List ClaimQ) (claimant : ClaimantId),
      graphDecide graph claims claimant = BinaryDecision.Deny := by
  classical
  by_contra hnone
  have hallPermit :
      ∀ (claims : List ClaimQ) (claimant : ClaimantId),
        graphDecide graph claims claimant = BinaryDecision.Permit := by
    intro claims claimant
    cases hdec : graphDecide graph claims claimant with
    | Permit => rfl
    | Deny =>
        exact False.elim (hnone ⟨claims, claimant, hdec⟩)
  have hall : AllLegitimacyAxioms graph := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro claims k j _hk _hj _hkj _hdist _hdeny
      rw [hallPermit claims j, hallPermit (removeClaimGraph k claims) j]
    · intro claims α hα j _hj
      rw [hallPermit claims j]
      change BinaryDecision.Permit =
        graphDecide graph
          (claims.map
            (fun c =>
              ⟨c.id, α * c.strength, mul_pos hα c.strength_pos, c.metadata⟩)) j
      rw [hallPermit
        (claims.map
          (fun c =>
            ⟨c.id, α * c.strength, mul_pos hα c.strength_pos, c.metadata⟩)) j]
    · intro claims k s' hs' j _hk _hdist _hle _hperm
      exact hallPermit (strengthenClaim k s' hs' claims) j
    · intro claims k s_r hs_r _hk _hdist _hperm
      exact hallPermit claims k
  exact hdetected (by
    cases failure <;> simp [AxiomFailureKind.satisfies] at hall ⊢
    · exact hall.1
    · exact hall.2.1
    · exact hall.2.2.1
    · exact hall.2.2.2)
/-- Every detected axiom failure also has some permitted decision in the original graph. If all decisions were denials, the axioms would again hold vacuously or by contradiction with the required permit premise, contradicting detection. This supplies the permit side of the mixed-decision witness. -/
theorem detected_failure_has_permitted_decision
    (graph : GovernanceGraph) (failure : AxiomFailureKind)
    (hdetected : failure.detected graph) :
    ∃ (claims : List ClaimQ) (claimant : ClaimantId),
      graphDecide graph claims claimant = BinaryDecision.Permit := by
  classical
  by_contra hnone
  have hallDeny :
      ∀ (claims : List ClaimQ) (claimant : ClaimantId),
        graphDecide graph claims claimant = BinaryDecision.Deny := by
    intro claims claimant
    cases hdec : graphDecide graph claims claimant with
    | Permit =>
        exact False.elim (hnone ⟨claims, claimant, hdec⟩)
    | Deny => rfl
  have hall : AllLegitimacyAxioms graph := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro claims k j _hk _hj _hkj _hdist _hdeny
      rw [hallDeny claims j, hallDeny (removeClaimGraph k claims) j]
    · intro claims α hα j _hj
      rw [hallDeny claims j]
      change BinaryDecision.Deny =
        graphDecide graph
          (claims.map
            (fun c =>
              ⟨c.id, α * c.strength, mul_pos hα c.strength_pos, c.metadata⟩)) j
      rw [hallDeny
        (claims.map
          (fun c =>
            ⟨c.id, α * c.strength, mul_pos hα c.strength_pos, c.metadata⟩)) j]
    · intro claims k s' hs' j _hk _hdist _hle hperm
      rw [hallDeny claims j] at hperm
      exact BinaryDecision.noConfusion hperm
    · intro claims k s_r hs_r _hk _hdist hperm
      rw [hallDeny (strengthenClaim k s_r hs_r claims) k] at hperm
      exact BinaryDecision.noConfusion hperm
  exact hdetected (by
    cases failure <;> simp [AxiomFailureKind.satisfies] at hall ⊢
    · exact hall.1
    · exact hall.2.1
    · exact hall.2.2.1
    · exact hall.2.2.2)
structure MixedDecisionWitness (graph : GovernanceGraph) where
  permitClaims : List ClaimQ
  permitClaimant : ClaimantId
  denyClaims : List ClaimQ
  denyClaimant : ClaimantId
  distinct_claimants : permitClaimant ≠ denyClaimant
  original_permit :
    graphDecide graph permitClaims permitClaimant = BinaryDecision.Permit
  original_deny :
    graphDecide graph denyClaims denyClaimant = BinaryDecision.Deny
/-- A detected failure yields a mixed-decision witness with distinct claimant slots. The proof combines the guaranteed permit and deny decisions, and if they occur at the same claimant it introduces an adjacent claimant to separate the permit and deny roles. This is the finite payload from which the profile-sensitive replacement repair chooses protected claimants. -/
theorem detected_failure_has_mixed_claimants_exists
    (graph : GovernanceGraph) (failure : AxiomFailureKind)
    (hdetected : failure.detected graph) :
    ∃ _ : MixedDecisionWitness graph, True := by
  classical
  rcases detected_failure_has_permitted_decision graph failure hdetected with
    ⟨permitClaims, permitClaimant, hpermit⟩
  rcases detected_failure_has_denied_decision graph failure hdetected with
    ⟨denyClaims, denyClaimant, hdeny⟩
  by_cases hsame : permitClaimant = denyClaimant
  · subst denyClaimant
    let alternate : ClaimantId := permitClaimant + 1
    have halt_ne_permit : alternate ≠ permitClaimant := by
      exact Nat.succ_ne_self permitClaimant
    cases halt : graphDecide graph denyClaims alternate with
    | Permit =>
        refine ⟨?_, trivial⟩
        exact
          { permitClaims := denyClaims
            permitClaimant := alternate
            denyClaims := denyClaims
            denyClaimant := permitClaimant
            distinct_claimants := halt_ne_permit
            original_permit := halt
            original_deny := hdeny }
    | Deny =>
        refine ⟨?_, trivial⟩
        exact
          { permitClaims := permitClaims
            permitClaimant := permitClaimant
            denyClaims := denyClaims
            denyClaimant := alternate
            distinct_claimants := by
              exact Nat.ne_of_lt (Nat.lt_succ_self permitClaimant)
            original_permit := hpermit
            original_deny := halt }
  · refine ⟨?_, trivial⟩
    exact
      { permitClaims := permitClaims
        permitClaimant := permitClaimant
        denyClaims := denyClaims
        denyClaimant := denyClaimant
        distinct_claimants := hsame
        original_permit := hpermit
        original_deny := hdeny }
noncomputable def detected_failure_mixed_claimants
    (graph : GovernanceGraph) (failure : AxiomFailureKind)
    (hdetected : failure.detected graph) :
    MixedDecisionWitness graph :=
  Classical.choose
    (detected_failure_has_mixed_claimants_exists graph failure hdetected)
/-- Claim membership is preserved when strengthening a possibly different claim. The induction follows the claim list and handles the updated claimant case separately, so downstream monotonicity and strategyproofness proofs can reuse membership evidence after a strength update. -/
theorem inClaims_strengthenClaim_of_inClaims
    {claims : List ClaimQ} {j k : ClaimantId} {s' : ℚ} {hs' : 0 < s'} :
    InClaims j claims → InClaims j (strengthenClaim k s' hs' claims) := by
  intro hj
  induction claims generalizing j with
  | nil =>
      obtain ⟨_, hmem, _⟩ := hj
      simp at hmem
  | cons c cs ih =>
      by_cases hck : c.id = k
      · simp [strengthenClaim, hck]
        obtain ⟨c', hc'mem, hc'id⟩ := hj
        cases hc'mem with
        | head =>
            exact ⟨⟨k, s', hs', c.metadata⟩, by simp, hck.symm.trans hc'id⟩
        | tail _ htail =>
            exact ⟨c', List.Mem.tail _ htail, hc'id⟩
      · simp [strengthenClaim, hck]
        obtain ⟨c', hc'mem, hc'id⟩ := hj
        cases hc'mem with
        | head =>
            exact ⟨c, by simp, hc'id⟩
        | tail _ htail =>
            rcases ih ⟨c', htail, hc'id⟩ with ⟨c'', hm, hid⟩
            exact ⟨c'', List.Mem.tail _ hm, hid⟩
/-- Claim membership is preserved by uniformly scaling all claim strengths by a positive rational. The mapped claim keeps the same identifier and has positive strength by multiplication, which is the membership fact used by the solidarity probe after rescaling. -/
theorem inClaims_scaled_of_inClaims
    {claims : List ClaimQ} {j : ClaimantId} {α : ℚ} (hα : 0 < α) :
    InClaims j claims →
      InClaims j
        (claims.map
          (fun c => c.scaleStrength α hα)) := by
  intro hj
  obtain ⟨c, hmem, hid⟩ := hj
  refine
    ⟨(fun c : ClaimQ => c.scaleStrength α hα) c, ?_, ?_⟩
  · exact List.mem_map_of_mem hmem
  · simpa using hid
def freshProfileClaimant (denied permitted : ClaimantId) : ClaimantId :=
  max denied permitted + 1
/-- The generated profile claimant is fresh relative to the denied claimant because it is strictly above the maximum of the protected pair. This small freshness fact is used to witness profile sensitivity outside the two protected claimant slots. -/
theorem freshProfileClaimant_ne_denied (denied permitted : ClaimantId) :
    freshProfileClaimant denied permitted ≠ denied := by
  exact Nat.ne_of_gt (Nat.lt_succ_of_le (Nat.le_max_left denied permitted))
/-- The generated profile claimant is also fresh relative to the permitted claimant, by the symmetric maximum bound. Together with the denied freshness lemma, it gives an outsider claimant for the non-collapse argument. -/
theorem freshProfileClaimant_ne_permitted (denied permitted : ClaimantId) :
    freshProfileClaimant denied permitted ≠ permitted := by
  exact Nat.ne_of_gt (Nat.lt_succ_of_le (Nat.le_max_right denied permitted))
def profileSensitiveRepairNode
    (denied permitted : ClaimantId) : GovernanceNodeFn :=
  fun claims claimant =>
    if claimant = denied then BinaryDecision.Deny
    else if claimant = permitted then BinaryDecision.Permit
    else if InClaims claimant claims then BinaryDecision.Permit
    else BinaryDecision.Deny
def profileSensitiveRepair
    (denied permitted : ClaimantId) : GovernanceGraph :=
  [profileSensitiveRepairNode denied permitted]
@[simp] theorem graphDecide_profileSensitiveRepair
    (denied permitted : ClaimantId) (claims : List ClaimQ) (claimant : ClaimantId) :
    graphDecide (profileSensitiveRepair denied permitted) claims claimant = if claimant = denied then BinaryDecision.Deny else if claimant = permitted then BinaryDecision.Permit else if InClaims claimant claims then BinaryDecision.Permit else BinaryDecision.Deny := by
  by_cases hdenied : claimant = denied
  · simp [profileSensitiveRepair, profileSensitiveRepairNode, graphDecide, hdenied]
  · by_cases hpermitted : claimant = permitted
    · simp [profileSensitiveRepair, profileSensitiveRepairNode, graphDecide, hpermitted, show permitted ≠ denied by exact fun h => hdenied (hpermitted.trans h)]
    · by_cases hmem : InClaims claimant claims <;> simp [profileSensitiveRepair, profileSensitiveRepairNode, graphDecide, hdenied, hpermitted, hmem]
/-- Proves `profileSensitiveRepair_agrees_on_profileRepairBranchAgreement` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem profileSensitiveRepair_agrees_on_profileRepairBranchAgreement
    (graph : GovernanceGraph) (denied permitted : ClaimantId) (p : List ClaimQ × ClaimantId) :
    ProfileRepairBranchAgreement graph denied permitted p → graphDecide (profileSensitiveRepair denied permitted) p.1 p.2 = graphDecide graph p.1 p.2 := by
  intro hp; rcases hp with ⟨hpdenied, hgraph⟩ | ⟨hpnotdenied, hppermitted, hgraph⟩ | ⟨hpnotdenied, hpnotpermitted, hmem, hgraph⟩ | ⟨hpnotdenied, hpnotpermitted, hmem, hgraph⟩
  · rw [hgraph]; simp [graphDecide_profileSensitiveRepair, hpdenied]
  · have hpermitted_not_denied : permitted ≠ denied := by intro h; exact hpnotdenied (hppermitted.trans h)
    rw [hgraph]; simp [graphDecide_profileSensitiveRepair, hppermitted, hpermitted_not_denied]
  · rw [hgraph]; simp [graphDecide_profileSensitiveRepair, hpnotdenied, hpnotpermitted, hmem]
  · rw [hgraph]; simp [graphDecide_profileSensitiveRepair, hpnotdenied, hpnotpermitted, hmem]
def twoPointProfileOppositeNode (denied permitted : ClaimantId) : GovernanceNodeFn :=
  fun claims claimant => if claimant = denied then match claims with | [] => BinaryDecision.Deny | _ :: _ => BinaryDecision.Permit else if claimant = permitted then match claims with | [] => BinaryDecision.Permit | _ :: _ => BinaryDecision.Deny else if InClaims claimant claims then BinaryDecision.Deny else BinaryDecision.Permit
def twoPointProfileOppositeGraph (denied permitted : ClaimantId) : GovernanceGraph := [twoPointProfileOppositeNode denied permitted]
/-- Proves `profileSensitiveRepair_twoPointOpposite_agreement_pair` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem profileSensitiveRepair_twoPointOpposite_agreement_pair
    {denied permitted : ClaimantId} (hdistinct : permitted ≠ denied) {claims : List ClaimQ} {claimant : ClaimantId} :
    graphDecide (profileSensitiveRepair denied permitted) claims claimant = graphDecide (twoPointProfileOppositeGraph denied permitted) claims claimant → (claims, claimant) = ([], denied) ∨ (claims, claimant) = ([], permitted) := by
  intro hagree; by_cases hdenied : claimant = denied
  · subst claimant; cases claims with | nil => exact Or.inl rfl | cons c cs => simp [twoPointProfileOppositeGraph, twoPointProfileOppositeNode, graphDecide_profileSensitiveRepair, graphDecide] at hagree
  · by_cases hpermitted : claimant = permitted
    · subst claimant; cases claims with | nil => exact Or.inr rfl | cons c cs => simp [twoPointProfileOppositeGraph, twoPointProfileOppositeNode, graphDecide_profileSensitiveRepair, graphDecide, hdistinct] at hagree
    · by_cases hmem : InClaims claimant claims <;> simp [twoPointProfileOppositeGraph, twoPointProfileOppositeNode, graphDecide_profileSensitiveRepair, graphDecide, hdenied, hpermitted, hmem] at hagree
/-- Proves `profileSensitiveRepair_twoPointOpposite_no_three_point_agreement_class` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem profileSensitiveRepair_twoPointOpposite_no_three_point_agreement_class
    {denied permitted : ClaimantId} (hdistinct : permitted ≠ denied) :
    ¬ ∃ (P : List ClaimQ × ClaimantId → Prop) (_ : DecidablePred P), (∃ p₁ p₂ p₃ : List ClaimQ × ClaimantId, P p₁ ∧ P p₂ ∧ P p₃ ∧ ThreePairwiseDistinct p₁ p₂ p₃) ∧ (∀ p : List ClaimQ × ClaimantId, P p → graphDecide (profileSensitiveRepair denied permitted) p.1 p.2 = graphDecide (twoPointProfileOppositeGraph denied permitted) p.1 p.2) := by
  rintro ⟨P, _hdec, ⟨⟨p₁, p₂, p₃, hp₁, hp₂, hp₃, hpairwise⟩, hagree⟩⟩
  have hp₁eq : p₁ = ([], denied) ∨ p₁ = ([], permitted) := by cases p₁ with | mk claims claimant => simpa using profileSensitiveRepair_twoPointOpposite_agreement_pair (denied := denied) (permitted := permitted) hdistinct (claims := claims) (claimant := claimant) (hagree _ hp₁)
  have hp₂eq : p₂ = ([], denied) ∨ p₂ = ([], permitted) := by cases p₂ with | mk claims claimant => simpa using profileSensitiveRepair_twoPointOpposite_agreement_pair (denied := denied) (permitted := permitted) hdistinct (claims := claims) (claimant := claimant) (hagree _ hp₂)
  have hp₃eq : p₃ = ([], denied) ∨ p₃ = ([], permitted) := by cases p₃ with | mk claims claimant => simpa using profileSensitiveRepair_twoPointOpposite_agreement_pair (denied := denied) (permitted := permitted) hdistinct (claims := claims) (claimant := claimant) (hagree _ hp₃)
  rcases hp₁eq with rfl | rfl <;> rcases hp₂eq with rfl | rfl <;> rcases hp₃eq with rfl | rfl <;> simp [ThreePairwiseDistinct, hdistinct, hdistinct.symm] at hpairwise
/-- Proves `no_three_point_agreement_class_for_profileSensitiveRepair_universal` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem no_three_point_agreement_class_for_profileSensitiveRepair_universal :
    ∀ (P : List ClaimQ × ClaimantId → Prop) [DecidablePred P], (∃ p₁ p₂ p₃, P p₁ ∧ P p₂ ∧ P p₃ ∧ ThreePairwiseDistinct p₁ p₂ p₃) →
      ∃ (graph : GovernanceGraph) (witness : MixedDecisionWitness graph), ¬ (∀ p, P p → graphDecide (profileSensitiveRepair witness.denyClaimant witness.permitClaimant) p.1 p.2 = graphDecide graph p.1 p.2) := by
  intro P hdec hthree
  let witness : MixedDecisionWitness (twoPointProfileOppositeGraph 1 0) :=
    { permitClaims := [], permitClaimant := 0, denyClaims := [], denyClaimant := 1, distinct_claimants := by norm_num, original_permit := by simp [twoPointProfileOppositeGraph, twoPointProfileOppositeNode, graphDecide], original_deny := by simp [twoPointProfileOppositeGraph, twoPointProfileOppositeNode, graphDecide] }
  refine ⟨twoPointProfileOppositeGraph 1 0, witness, ?_⟩
  intro hagree
  apply profileSensitiveRepair_twoPointOpposite_no_three_point_agreement_class (denied := 1) (permitted := 0) (by norm_num)
  refine ⟨P, hdec, hthree, ?_⟩
  intro p hp
  simpa [witness] using hagree p hp
/-- Proves `profileSensitiveRepair_allLegitimacyAxioms` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem profileSensitiveRepair_allLegitimacyAxioms (denied permitted : ClaimantId) :
    AllLegitimacyAxioms (profileSensitiveRepair denied permitted) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro claims k j _hk hj hkj _hdist _hdeny
    by_cases hjdenied : j = denied
    · simp [graphDecide_profileSensitiveRepair, hjdenied]
    · by_cases hjpermitted : j = permitted
      · simp [graphDecide_profileSensitiveRepair, hjpermitted, show permitted ≠ denied by exact fun h => hjdenied (hjpermitted.trans h)]
      · have hj_removed : InClaims j (removeClaimGraph k claims) := inClaims_removeClaimGraph_of_ne hkj.symm hj
        simp [graphDecide_profileSensitiveRepair, hjdenied, hjpermitted, hj, hj_removed]
  · intro claims α hα j hj
    by_cases hjdenied : j = denied
    · simp [graphDecide_profileSensitiveRepair, hjdenied]
    · by_cases hjpermitted : j = permitted
      · simp [graphDecide_profileSensitiveRepair, hjpermitted, show permitted ≠ denied by exact fun h => hjdenied (hjpermitted.trans h)]
      · have hj_scaled := inClaims_scaled_of_inClaims (j := j) hα hj
        simp [graphDecide_profileSensitiveRepair, hjdenied, hjpermitted, hj, hj_scaled]
  · intro claims k s' hs' j _hk _hdist _hle hperm
    by_cases hjdenied : j = denied
    · simp [graphDecide_profileSensitiveRepair, hjdenied] at hperm
    · by_cases hjpermitted : j = permitted
      · simp [graphDecide_profileSensitiveRepair, hjpermitted, show permitted ≠ denied by exact fun h => hjdenied (hjpermitted.trans h)]
      · by_cases hj : InClaims j claims
        · have hj_strengthened : InClaims j (strengthenClaim k s' hs' claims) := inClaims_strengthenClaim_of_inClaims hj
          simp [graphDecide_profileSensitiveRepair, hjdenied, hjpermitted, hj_strengthened]
        · simp [graphDecide_profileSensitiveRepair, hjdenied, hjpermitted, hj] at hperm
  · intro claims k s_r hs_r hk _hdist hperm
    by_cases hkdenied : k = denied
    · simp [graphDecide_profileSensitiveRepair, hkdenied] at hperm
    · by_cases hkpermitted : k = permitted
      · simp [graphDecide_profileSensitiveRepair, hkpermitted, show permitted ≠ denied by exact fun h => hkdenied (hkpermitted.trans h)]
      · simp [graphDecide_profileSensitiveRepair, hkdenied, hkpermitted, hk]
/-- Proves `profileSensitiveRepair_dense_profile_sensitivity` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem profileSensitiveRepair_dense_profile_sensitivity
    {denied permitted : ClaimantId} (hdistinct : permitted ≠ denied) :
    ∃ protectedDeny protectedPermit : ClaimantId, protectedDeny ≠ protectedPermit ∧ ∀ outsider : ClaimantId, outsider ≠ protectedDeny → outsider ≠ protectedPermit → ∃ claims₁ claims₂ : List ClaimQ, graphDecide (profileSensitiveRepair denied permitted) claims₁ outsider ≠ graphDecide (profileSensitiveRepair denied permitted) claims₂ outsider := by
  refine ⟨denied, permitted, hdistinct.symm, ?_⟩
  intro outsider houtsider_denied houtsider_permitted
  refine ⟨[], singletonClaimProfile outsider 1 (by norm_num), ?_⟩
  simp [graphDecide_profileSensitiveRepair, houtsider_denied, houtsider_permitted, InClaims, singletonClaimProfile]
/-- Proves `profileSensitiveRepair_not_behaviorally_collapse` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem profileSensitiveRepair_not_behaviorally_collapse
    (denied permitted : ClaimantId) :
    ¬ ∃ d : ClaimantId → BinaryDecision, ∀ claims claimant, graphDecide (profileSensitiveRepair denied permitted) claims claimant = d claimant := by
  intro hcollapse
  rcases hcollapse with ⟨d, hd⟩
  let fresh := freshProfileClaimant denied permitted
  have hfresh_denied : fresh ≠ denied := freshProfileClaimant_ne_denied denied permitted
  have hfresh_permitted : fresh ≠ permitted := freshProfileClaimant_ne_permitted denied permitted
  have hnil := hd [] fresh
  have hsingleton := hd (singletonClaimProfile fresh 1 (by norm_num)) fresh
  simp [graphDecide_profileSensitiveRepair, hfresh_denied, hfresh_permitted, InClaims, singletonClaimProfile] at hnil hsingleton
  exact BinaryDecision.noConfusion (hnil.trans hsingleton.symm)
/-- Proves `profileSensitiveRepair_behavioral_non_collapse` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem profileSensitiveRepair_behavioral_non_collapse
    {denied permitted : ClaimantId} (hdistinct : permitted ≠ denied) :
    ∃ (claims : List ClaimQ) (claimant₁ claimant₂ : ClaimantId), graphDecide (profileSensitiveRepair denied permitted) claims claimant₁ ≠ graphDecide (profileSensitiveRepair denied permitted) claims claimant₂ := by
  refine ⟨[], permitted, denied, ?_⟩
  simp [graphDecide_profileSensitiveRepair, hdistinct]
/-- Scoped replacement constructor: axiom satisfaction plus `NonTrivialRepairFaithfulness`, not behavior-preserving repair beyond that predicate. -/
noncomputable def nonCollapsedReplacementRepair (graph : GovernanceGraph) (failure : AxiomFailureKind) : GovernanceGraph := by
  classical
  exact if hdetected : failure.detected graph then let witness := detected_failure_mixed_claimants graph failure hdetected; profileSensitiveRepair witness.denyClaimant witness.permitClaimant else []
/-- Proves `nonCollapsedReplacementRepair_eq_of_detected` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem nonCollapsedReplacementRepair_eq_of_detected
    (graph : GovernanceGraph) (failure : AxiomFailureKind)
    (hdetected : failure.detected graph) :
    nonCollapsedReplacementRepair graph failure =
      profileSensitiveRepair
        (detected_failure_mixed_claimants graph failure hdetected).denyClaimant
        (detected_failure_mixed_claimants graph failure hdetected).permitClaimant := by
  simp [nonCollapsedReplacementRepair, hdetected]
/-- Proves `nonCollapsedReplacementRepair_allLegitimacyAxioms` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem nonCollapsedReplacementRepair_allLegitimacyAxioms
    (graph : GovernanceGraph) (failure : AxiomFailureKind) :
    AllLegitimacyAxioms (nonCollapsedReplacementRepair graph failure) := by
  classical
  by_cases hdetected : failure.detected graph
  · rw [nonCollapsedReplacementRepair_eq_of_detected graph failure hdetected]
    exact profileSensitiveRepair_allLegitimacyAxioms
      (detected_failure_mixed_claimants graph failure hdetected).denyClaimant
      (detected_failure_mixed_claimants graph failure hdetected).permitClaimant
  · simpa [nonCollapsedReplacementRepair, hdetected] using emptyGraph_allLegitimacyAxioms
/-- Proves `nonCollapsedReplacementRepair_satisfies` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem nonCollapsedReplacementRepair_satisfies
    (graph : GovernanceGraph) (failure target : AxiomFailureKind) :
    target.satisfies (nonCollapsedReplacementRepair graph failure) := by
  have hall := nonCollapsedReplacementRepair_allLegitimacyAxioms graph failure
  cases target <;> simp [AxiomFailureKind.satisfies] at hall ⊢
  · exact hall.1
  · exact hall.2.1
  · exact hall.2.2.1
  · exact hall.2.2.2
/-- Proves `nonCollapsedReplacementRepair_preserves_other_passes` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem nonCollapsedReplacementRepair_preserves_other_passes
    (graph : GovernanceGraph) (failure : AxiomFailureKind) :
    OtherAxiomPassesPreserved graph
      (nonCollapsedReplacementRepair graph failure) failure := by
  intro other _hne _hpass
  exact nonCollapsedReplacementRepair_satisfies graph failure other
/-- Proves `nonCollapsedReplacementRepair_faithful_of_detected` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem nonCollapsedReplacementRepair_faithful_of_detected
    (graph : GovernanceGraph) (failure : AxiomFailureKind)
    (hdetected : failure.detected graph) :
    NonTrivialRepairFaithfulness graph
      (nonCollapsedReplacementRepair graph failure) := by
  classical
  let witness := detected_failure_mixed_claimants graph failure hdetected
  have hrepair :
      nonCollapsedReplacementRepair graph failure =
        profileSensitiveRepair witness.denyClaimant witness.permitClaimant := by
    simpa [witness] using
      nonCollapsedReplacementRepair_eq_of_detected graph failure hdetected
  refine
    { not_behaviorally_collapse := ?_
      preserves_mixed_decision_seed_subset := ?_
      preserves_characterizable_subset := ?_
      behavioral_non_collapse := ?_
      dense_profile_sensitivity := ?_ }
  · intro hcollapse
    apply profileSensitiveRepair_not_behaviorally_collapse
      witness.denyClaimant witness.permitClaimant
    rcases hcollapse with ⟨d, hd⟩
    refine ⟨d, ?_⟩
    intro claims claimant
    rw [← hrepair]
    exact hd claims claimant
  · let S : Set (List ClaimQ × ClaimantId) :=
      fun p =>
        p = (witness.denyClaims, witness.denyClaimant) ∨
          p = (witness.permitClaims, witness.permitClaimant)
    refine ⟨S, ?_, ?_, ?_, ?_⟩
    · exact ⟨(witness.denyClaims, witness.denyClaimant), Or.inl rfl⟩
    · intro p hp
      rcases hp with hp | hp
      · subst p
        rw [hrepair, witness.original_deny]
        simp [graphDecide_profileSensitiveRepair]
      · subst p
        rw [hrepair, witness.original_permit]
        simp [graphDecide_profileSensitiveRepair, witness.distinct_claimants]
    · exact
        ⟨(witness.denyClaims, witness.denyClaimant), Or.inl rfl,
          witness.original_deny⟩
    · exact
        ⟨(witness.permitClaims, witness.permitClaimant), Or.inr rfl,
          witness.original_permit⟩
  · let P : List ClaimQ × ClaimantId → Prop :=
      ProfileRepairBranchAgreement graph witness.denyClaimant
        witness.permitClaimant
    refine ⟨witness.denyClaimant, witness.permitClaimant, witness.distinct_claimants.symm, P, inferInstance, ?_, ?_, ?_, ?_⟩
    · intro p; rfl
    · intro p hp; rw [hrepair]; exact profileSensitiveRepair_agrees_on_profileRepairBranchAgreement graph witness.denyClaimant witness.permitClaimant p hp
    · exact ⟨(witness.denyClaims, witness.denyClaimant), Or.inl ⟨rfl, witness.original_deny⟩, witness.original_deny⟩
    · exact ⟨(witness.permitClaims, witness.permitClaimant), Or.inr (Or.inl ⟨witness.distinct_claimants, rfl, witness.original_permit⟩), witness.original_permit⟩
  · rw [hrepair]
    exact profileSensitiveRepair_behavioral_non_collapse
      witness.distinct_claimants
  · rw [hrepair]
    exact profileSensitiveRepair_dense_profile_sensitivity
      witness.distinct_claimants
/-- Proves `lookupStrength_strengthenClaim_of_ne` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem lookupStrength_strengthenClaim_of_ne
    {claims : List ClaimQ} {j k : ClaimantId} {s' : ℚ} {hs' : 0 < s'}
    (hjk : j ≠ k) :
    lookupStrength j (strengthenClaim k s' hs' claims) =
      lookupStrength j claims := by
  induction claims with
  | nil =>
      simp [lookupStrength, strengthenClaim]
  | cons c cs ih =>
      by_cases hck : c.id = k
      · have hcj : c.id ≠ j := by
          intro hcj
          exact hjk (hcj.symm.trans hck)
        have hkj : k ≠ j := by
          intro hkj
          exact hjk hkj.symm
        simp [strengthenClaim, hck, lookupStrength, hkj]
      · by_cases hcj : c.id = j
        · simp [strengthenClaim, lookupStrength, hcj, hjk]
        · simp [strengthenClaim, hck, lookupStrength, hcj, ih]
/-- Substantive witness via non-collapsed profile-sensitive replacement, with no general behavioral-preservation claim. -/
theorem substantive_nonCollapsedReplacementRepair_for_detected
    (graph : GovernanceGraph) (failure : AxiomFailureKind)
    (hdetected : failure.detected graph) :
    SubstantiveRepairExists graph failure := by
  refine ⟨?_, trivial⟩
  exact
    { repaired := nonCollapsedReplacementRepair graph failure
      detects_failure := hdetected
      closes_failure := nonCollapsedReplacementRepair_satisfies graph failure failure
      preserves_other_passes :=
        nonCollapsedReplacementRepair_preserves_other_passes graph failure
      faithfulness :=
        nonCollapsedReplacementRepair_faithful_of_detected graph failure hdetected }
abbrev monotonicityProbeGraph : GovernanceGraph :=
  peerGraph
/-- The peer graph is the monotonicity probe: it satisfies the concrete counterexample already isolated by `peerGraph_not_monotone`. This theorem marks that graph as a detected monotonicity failure so the generic non-collapsed repair constructor can be applied to the probe. -/
theorem monotonicityProbeGraph_detects_failure :
    AxiomFailureKind.detected .monotonicity_violation
      monotonicityProbeGraph :=
  peerGraph_not_monotone
/-- The detected monotonicity probe admits a substantive non-collapsed repair. The proof is an application of the generic replacement constructor, so the result records existence of an axiom-satisfying repaired graph together with the scoped faithfulness and other-pass obligations rather than strict decision preservation. -/
theorem monotonicityProbe_substantiveRepairExists :
    SubstantiveRepairExists monotonicityProbeGraph
      .monotonicity_violation :=
  substantive_nonCollapsedReplacementRepair_for_detected monotonicityProbeGraph
    .monotonicity_violation monotonicityProbeGraph_detects_failure
def consistencyProbeShortListNode : GovernanceNodeFn := fun claims _ =>
  if claims.length ≤ 2 then BinaryDecision.Permit else BinaryDecision.Deny
def consistencyProbeGraph : GovernanceGraph :=
  [consistencyProbeShortListNode]
/-- Proves `consistencyProbeGraph_solidary` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem consistencyProbeGraph_solidary :
    GraphSolidarity consistencyProbeGraph := by
  intro claims α hα j hj
  simp [consistencyProbeGraph, consistencyProbeShortListNode, graphDecide]
/-- Proves `consistencyProbeGraph_monotone` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem consistencyProbeGraph_monotone :
    GraphMonotonicity consistencyProbeGraph := by
  intro claims k s' hs' j hk hdist hle hperm
  simpa [consistencyProbeGraph, consistencyProbeShortListNode, graphDecide,
    strengthenClaim_length] using hperm
/-- Proves `consistencyProbeGraph_strategyproof` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem consistencyProbeGraph_strategyproof :
    GraphStrategyproofness consistencyProbeGraph := by
  intro claims k s_r hs_r hk hdist hperm
  simpa [consistencyProbeGraph, consistencyProbeShortListNode, graphDecide,
    strengthenClaim_length] using hperm
def consistencyProbeA : ClaimQ := ⟨0, 1 / 4, by norm_num, []⟩
def consistencyProbeB : ClaimQ := ⟨1, 1 / 2, by norm_num, []⟩
def consistencyProbeC : ClaimQ := ⟨2, 3 / 4, by norm_num, []⟩
def consistencyProbeClaims : List ClaimQ :=
  [consistencyProbeA, consistencyProbeB, consistencyProbeC]
theorem consistencyProbeA_in :
    InClaims 0 consistencyProbeClaims :=
  ⟨consistencyProbeA, by simp [consistencyProbeClaims], rfl⟩
theorem consistencyProbeB_in :
    InClaims 1 consistencyProbeClaims :=
  ⟨consistencyProbeB, by simp [consistencyProbeClaims], rfl⟩
/-- Proves `consistencyProbeClaims_distinct` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem consistencyProbeClaims_distinct :
    ClaimsDistinct consistencyProbeClaims := by
  unfold ClaimsDistinct consistencyProbeClaims consistencyProbeA
    consistencyProbeB consistencyProbeC
  decide
/-- The short-list consistency probe realizes a concrete consistency failure. Three distinct claims make the graph deny claimant `1`, while removing claimant `0` flips that decision to permit; this contradicts the consistency axiom's removal stability requirement. The theorem packages that finite calculation as the detected failure used by the repair witness. -/
theorem consistencyProbeGraph_detects_failure :
    AxiomFailureKind.detected .consistency_violation
      consistencyProbeGraph := by
  intro hcons
  have h :=
    hcons consistencyProbeClaims 0 1
      consistencyProbeA_in consistencyProbeB_in
      (by decide)
      consistencyProbeClaims_distinct
      (by native_decide)
  rw [show graphDecide consistencyProbeGraph consistencyProbeClaims 1 =
      BinaryDecision.Deny by native_decide] at h
  rw [show graphDecide consistencyProbeGraph
      (removeClaimGraph 0 consistencyProbeClaims) 1 =
      BinaryDecision.Permit by native_decide] at h
  exact BinaryDecision.noConfusion h
/-- Proves `consistencyProbeGraph_other_passes` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem consistencyProbeGraph_other_passes :
    GraphSolidarity consistencyProbeGraph ∧
      GraphMonotonicity consistencyProbeGraph ∧
        GraphStrategyproofness consistencyProbeGraph :=
  ⟨consistencyProbeGraph_solidary,
    consistencyProbeGraph_monotone,
    consistencyProbeGraph_strategyproof⟩
/-- The consistency probe has a substantive repair witness after its detected failure is supplied. The conclusion is the four-field `SubstantiveRepairExists` package: satisfaction of the failed axiom, avoidance of claimant-constant collapse, preservation of the other probe axes, and the nontrivial faithfulness condition. -/
theorem consistencyProbe_substantiveRepairExists :
    SubstantiveRepairExists consistencyProbeGraph
      .consistency_violation :=
  substantive_nonCollapsedReplacementRepair_for_detected consistencyProbeGraph
    .consistency_violation consistencyProbeGraph_detects_failure
def solidarityProbeAbsoluteSupportNode : GovernanceNodeFn := fun claims k =>
  if k = 1 then
    if lookupStrength 0 claims + lookupStrength 2 claims ≥ 1 then
      BinaryDecision.Permit
    else
      BinaryDecision.Deny
  else
    BinaryDecision.Permit
def solidarityProbeGraph : GovernanceGraph :=
  [solidarityProbeAbsoluteSupportNode]
/-- Proves `solidarityProbeGraph_consistent` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem solidarityProbeGraph_consistent :
    GraphConsistency solidarityProbeGraph := by
  intro claims k j hk hj hkj hdist hdeny
  have hk_one : k = 1 := by
    by_cases hk1 : k = 1
    · exact hk1
    · simp [solidarityProbeGraph, solidarityProbeAbsoluteSupportNode,
        graphDecide, hk1] at hdeny
  subst k
  have hj_ne : j ≠ 1 := by simpa using hkj.symm
  simp [solidarityProbeGraph, solidarityProbeAbsoluteSupportNode,
    graphDecide, hj_ne]
/-- Proves `solidarityProbeGraph_monotone` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem solidarityProbeGraph_monotone :
    GraphMonotonicity solidarityProbeGraph := by
  intro claims k s' hs' j hk hdist hle hperm
  by_cases hj : j = 1
  · subst j
    have hbase :
        lookupStrength 0 claims + lookupStrength 2 claims ≥ 1 := by
      by_cases hcond : 1 ≤ lookupStrength 0 claims + lookupStrength 2 claims
      · exact hcond
      · simp [solidarityProbeGraph, solidarityProbeAbsoluteSupportNode,
          graphDecide, hcond] at hperm
    by_cases hk0 : k = 0
    · subst k
      have hkbound :
          lookupStrength 0 claims ≤ s' :=
        lookupStrength_le_of_all_le hk hle
      have hnew :
          lookupStrength 0 (strengthenClaim 0 s' hs' claims) +
              lookupStrength 2 (strengthenClaim 0 s' hs' claims) ≥ 1 := by
        rw [show lookupStrength 0 (strengthenClaim 0 s' hs' claims) = s' by
              exact lookupStrength_after_strengthen hk hdist,
            show lookupStrength 2 (strengthenClaim 0 s' hs' claims) =
                lookupStrength 2 claims by
              exact lookupStrength_strengthenClaim_of_ne
                (j := 2) (k := 0) (s' := s') (hs' := hs') (by decide)]
        linarith
      simp [solidarityProbeGraph, solidarityProbeAbsoluteSupportNode,
        graphDecide, hnew]
    · by_cases hk2 : k = 2
      · subst k
        have hkbound :
            lookupStrength 2 claims ≤ s' :=
          lookupStrength_le_of_all_le hk hle
        have hnew :
            lookupStrength 0 (strengthenClaim 2 s' hs' claims) +
                lookupStrength 2 (strengthenClaim 2 s' hs' claims) ≥ 1 := by
          rw [show lookupStrength 0 (strengthenClaim 2 s' hs' claims) =
                  lookupStrength 0 claims by
                exact lookupStrength_strengthenClaim_of_ne
                  (j := 0) (k := 2) (s' := s') (hs' := hs') (by decide),
              show lookupStrength 2 (strengthenClaim 2 s' hs' claims) = s' by
                exact lookupStrength_after_strengthen hk hdist]
          linarith
        simp [solidarityProbeGraph, solidarityProbeAbsoluteSupportNode,
          graphDecide, hnew]
      · have hsame0 :
            lookupStrength 0 (strengthenClaim k s' hs' claims) =
              lookupStrength 0 claims := by
          exact lookupStrength_strengthenClaim_of_ne
            (j := 0) (k := k) (s' := s') (hs' := hs')
            (by intro h; exact hk0 h.symm)
        have hsame2 :
            lookupStrength 2 (strengthenClaim k s' hs' claims) =
              lookupStrength 2 claims := by
          exact lookupStrength_strengthenClaim_of_ne
            (j := 2) (k := k) (s' := s') (hs' := hs')
            (by intro h; exact hk2 h.symm)
        simp [solidarityProbeGraph, solidarityProbeAbsoluteSupportNode,
          graphDecide, hsame0, hsame2, hbase]
  · exact by
      simp [solidarityProbeGraph, solidarityProbeAbsoluteSupportNode,
        graphDecide, hj]
/-- Proves `solidarityProbeGraph_strategyproof` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem solidarityProbeGraph_strategyproof :
    GraphStrategyproofness solidarityProbeGraph := by
  intro claims k s_r hs_r hk hdist hperm
  by_cases hk1 : k = 1
  · subst k
    have hperm' :
        lookupStrength 0 (strengthenClaim 1 s_r hs_r claims) +
            lookupStrength 2 (strengthenClaim 1 s_r hs_r claims) ≥ 1 := by
      by_cases hcond :
          1 ≤ lookupStrength 0 (strengthenClaim 1 s_r hs_r claims) +
            lookupStrength 2 (strengthenClaim 1 s_r hs_r claims)
      · exact hcond
      · simp [solidarityProbeGraph, solidarityProbeAbsoluteSupportNode,
          graphDecide, hcond] at hperm
    have hbase :
        lookupStrength 0 claims + lookupStrength 2 claims ≥ 1 := by
      rw [lookupStrength_strengthenClaim_of_ne
          (j := 0) (k := 1) (s' := s_r) (hs' := hs_r) (by decide),
        lookupStrength_strengthenClaim_of_ne
          (j := 2) (k := 1) (s' := s_r) (hs' := hs_r) (by decide)] at hperm'
      exact hperm'
    simp [solidarityProbeGraph, solidarityProbeAbsoluteSupportNode,
      graphDecide, hbase]
  · simp [solidarityProbeGraph, solidarityProbeAbsoluteSupportNode,
      graphDecide, hk1]
def solidarityProbeA : ClaimQ := ⟨0, 1 / 4, by norm_num, []⟩
def solidarityProbeB : ClaimQ := ⟨1, 1 / 4, by norm_num, []⟩
def solidarityProbeC : ClaimQ := ⟨2, 1 / 4, by norm_num, []⟩
def solidarityProbeClaims : List ClaimQ :=
  [solidarityProbeA, solidarityProbeB, solidarityProbeC]
/-- The absolute-support solidarity probe detects a scale-sensitivity failure. The base claim list denies claimant `1`, but uniformly doubling the finite claim strengths makes the same claimant permitted, contradicting solidarity. This theorem records that finite calculation as the detected solidarity failure. -/
theorem solidarityProbeGraph_detects_failure :
    AxiomFailureKind.detected .solidarity_violation
      solidarityProbeGraph := by
  intro hsol
  let scaled : List ClaimQ :=
    solidarityProbeClaims.map
      (fun c => (⟨c.id, (2 : ℚ) * c.strength, by
        have hc := c.strength_pos
        nlinarith, c.metadata⟩ : ClaimQ))
  have h :=
    hsol solidarityProbeClaims 2 (by norm_num) 1
      (by exact ⟨solidarityProbeB, by simp [solidarityProbeClaims], rfl⟩)
  change graphDecide solidarityProbeGraph solidarityProbeClaims 1 =
    graphDecide solidarityProbeGraph scaled 1 at h
  rw [show graphDecide solidarityProbeGraph solidarityProbeClaims 1 =
      BinaryDecision.Deny by native_decide] at h
  rw [show graphDecide solidarityProbeGraph scaled 1 =
      BinaryDecision.Permit by native_decide] at h
  exact BinaryDecision.noConfusion h
/-- Proves `solidarityProbeGraph_other_passes` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem solidarityProbeGraph_other_passes :
    GraphConsistency solidarityProbeGraph ∧
      GraphMonotonicity solidarityProbeGraph ∧
        GraphStrategyproofness solidarityProbeGraph :=
  ⟨solidarityProbeGraph_consistent,
    solidarityProbeGraph_monotone,
    solidarityProbeGraph_strategyproof⟩
/-- The solidarity probe admits the same substantive repair package once its scale-sensitivity failure is detected. The witness repairs the solidarity axis while preserving the other checked axioms and maintaining nontrivial faithfulness, so it is not a claimant-constant collapse. -/
theorem solidarityProbe_substantiveRepairExists :
    SubstantiveRepairExists solidarityProbeGraph
      .solidarity_violation :=
  substantive_nonCollapsedReplacementRepair_for_detected solidarityProbeGraph
    .solidarity_violation solidarityProbeGraph_detects_failure
def strategyproofnessBridgeProbeOwnThresholdNode : GovernanceNodeFn :=
  fun claims k =>
    if (1 : ℚ) ≤ lookupStrength k claims then
      BinaryDecision.Permit
    else
      BinaryDecision.Deny
def strategyproofnessBridgeProbeGraph : GovernanceGraph :=
  [strategyproofnessBridgeProbeOwnThresholdNode]
/-- Proves `strategyproofnessBridgeProbeGraph_consistent` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem strategyproofnessBridgeProbeGraph_consistent :
    GraphConsistency strategyproofnessBridgeProbeGraph := by
  intro claims k j _hk _hj hkj _hdist _hdeny
  have hlookup :
      lookupStrength j (removeClaimGraph k claims) =
        lookupStrength j claims := by
    exact lookupStrength_removeClaimGraph_of_ne
      (by intro h; exact hkj h.symm)
  by_cases hbase : (1 : ℚ) ≤ lookupStrength j claims
  · simp [strategyproofnessBridgeProbeGraph,
      strategyproofnessBridgeProbeOwnThresholdNode, graphDecide,
      hbase, hlookup]
  · simp [strategyproofnessBridgeProbeGraph,
      strategyproofnessBridgeProbeOwnThresholdNode, graphDecide,
      hbase, hlookup]
/-- Proves `strategyproofnessBridgeProbeGraph_monotone` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem strategyproofnessBridgeProbeGraph_monotone :
    GraphMonotonicity strategyproofnessBridgeProbeGraph := by
  intro claims k s' hs' j hk hdist hle hperm
  have hbase : (1 : ℚ) ≤ lookupStrength j claims := by
    by_cases hcond : (1 : ℚ) ≤ lookupStrength j claims
    · exact hcond
    · simp [strategyproofnessBridgeProbeGraph,
        strategyproofnessBridgeProbeOwnThresholdNode, graphDecide,
        hcond] at hperm
  by_cases hjk : j = k
  · subst j
    have hbound : lookupStrength k claims ≤ s' :=
      lookupStrength_le_of_all_le hk hle
    have hnew :
        (1 : ℚ) ≤ lookupStrength k
          (strengthenClaim k s' hs' claims) := by
      rw [lookupStrength_after_strengthen hk hdist]
      linarith
    simp [strategyproofnessBridgeProbeGraph,
      strategyproofnessBridgeProbeOwnThresholdNode, graphDecide, hnew]
  · have hsame :
        lookupStrength j (strengthenClaim k s' hs' claims) =
          lookupStrength j claims :=
      lookupStrength_strengthenClaim_of_ne hjk
    simp [strategyproofnessBridgeProbeGraph,
      strategyproofnessBridgeProbeOwnThresholdNode, graphDecide,
      hbase, hsame]
def strategyproofnessBridgeProbeA : ClaimQ :=
  ⟨0, 1 / 2, by norm_num, []⟩
def strategyproofnessBridgeProbeClaims : List ClaimQ :=
  [strategyproofnessBridgeProbeA]
theorem strategyproofnessBridgeProbeA_in :
    InClaims 0 strategyproofnessBridgeProbeClaims :=
  ⟨strategyproofnessBridgeProbeA,
    by simp [strategyproofnessBridgeProbeClaims], rfl⟩
/-- Proves `strategyproofnessBridgeProbeClaims_distinct` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem strategyproofnessBridgeProbeClaims_distinct :
    ClaimsDistinct strategyproofnessBridgeProbeClaims := by
  unfold ClaimsDistinct strategyproofnessBridgeProbeClaims
    strategyproofnessBridgeProbeA
  decide
/-- Proves `strategyproofnessBridgeProbeGraph_detects_failure` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem strategyproofnessBridgeProbeGraph_detects_failure :
    AxiomFailureKind.detected .strategyproofness_bridge_violation
      strategyproofnessBridgeProbeGraph := by
  intro hsp
  have h :=
    hsp strategyproofnessBridgeProbeClaims 0 1 (by norm_num)
      strategyproofnessBridgeProbeA_in
      strategyproofnessBridgeProbeClaims_distinct
      (by native_decide)
  rw [show graphDecide strategyproofnessBridgeProbeGraph
      strategyproofnessBridgeProbeClaims 0 = BinaryDecision.Deny
      by native_decide] at h
  exact BinaryDecision.noConfusion h
/-- Proves `strategyproofnessBridgeProbeGraph_other_passes` for the scoped universal-repair witness or obstruction; it does not assert unrestricted behavior-preserving repair. -/
theorem strategyproofnessBridgeProbeGraph_other_passes :
    GraphConsistency strategyproofnessBridgeProbeGraph ∧
      GraphMonotonicity strategyproofnessBridgeProbeGraph :=
  ⟨strategyproofnessBridgeProbeGraph_consistent,
    strategyproofnessBridgeProbeGraph_monotone⟩
/-- Strategyproofness is not isolated from the other two positive probes in this bridge. Any graph that is both solidary and monotone already satisfies strategyproofness by the imported implication, so there is no graph witnessing only a strategyproofness failure while those two axioms pass. This explains why the strategyproofness probe is a bridge failure rather than an independent single-axis counterexample. -/
theorem strategyproofness_bridge_failure_not_isolable :
    ¬ ∃ graph : GovernanceGraph,
      GraphSolidarity graph ∧ GraphMonotonicity graph ∧
        ¬ GraphStrategyproofness graph := by
  intro h
  rcases h with ⟨graph, hsolidarity, hmonotone, hnotStrategyproof⟩
  exact hnotStrategyproof
    (solidarity_monotonicity_imply_strategyproof hsolidarity hmonotone)
/-- The strategyproofness-bridge probe still has a substantive repair witness. Its failure is detected on the own-threshold graph, and the generic non-collapsed replacement supplies an axiom-satisfying repair with the scoped faithfulness and other-pass guarantees expected by `SubstantiveRepairExists`. -/
theorem strategyproofnessBridgeProbe_substantiveRepairExists :
    SubstantiveRepairExists strategyproofnessBridgeProbeGraph
      .strategyproofness_bridge_violation :=
  substantive_nonCollapsedReplacementRepair_for_detected strategyproofnessBridgeProbeGraph
    .strategyproofness_bridge_violation
    strategyproofnessBridgeProbeGraph_detects_failure
/-- Uniform diagnostic coverage for detected graph failures. For every graph and every failure kind, a detected failure can be routed through the non-collapsed replacement constructor to obtain a substantive repair witness. This is the file's positive existence theorem at the weaker faithfulness bar, not a strict behavior-preservation theorem. -/
theorem nonCollapsedReplacementRepair_graphDiagnostic_all_failure_classes_supported :
    ∀ (graph : GovernanceGraph) (failure : AxiomFailureKind),
      failure.detected graph → SubstantiveRepairExists graph failure :=
  substantive_nonCollapsedReplacementRepair_for_detected
/-- All four finite repair probes succeed at the substantive witness level. The conclusion packages monotonicity, consistency, solidarity, and strategyproofness-bridge examples as a four-conjunct existence statement, each inhabited by the corresponding non-collapsed replacement repair. Operationally, this demonstrates broad repair coverage without claiming exact preservation of the original decision function. -/
theorem substantiveRepair_all_probes_succeed :
    SubstantiveRepairExists monotonicityProbeGraph
        .monotonicity_violation ∧
      SubstantiveRepairExists consistencyProbeGraph
        .consistency_violation ∧
      SubstantiveRepairExists solidarityProbeGraph
        .solidarity_violation ∧
      SubstantiveRepairExists strategyproofnessBridgeProbeGraph
        .strategyproofness_bridge_violation :=
  ⟨monotonicityProbe_substantiveRepairExists,
    consistencyProbe_substantiveRepairExists,
    solidarityProbe_substantiveRepairExists,
    strategyproofnessBridgeProbe_substantiveRepairExists⟩
/-- Nontrivial faithfulness rules out a universal claimant-constant repair scheme. The hypothesis allows a repair function that closes every detected failure, but also requires every repaired graph to satisfy `NonTrivialRepairFaithfulness`; applying it to the monotonicity probe contradicts the witness field forbidding behavioral collapse to a claimant-only decision table. This obstruction is weaker than strict preservation but still blocks the trivial constant repair strategy. -/
theorem no_universal_claimant_constant_collapse_under_nontrivial_faithfulness :
    ¬ ∃ R : GovernanceGraph → GovernanceGraph,
      (∀ graph : GovernanceGraph,
        ∃ d : ClaimantId → BinaryDecision, R graph = claimantConstGraph d) ∧
      ∀ (graph : GovernanceGraph) (failure : AxiomFailureKind),
        failure.detected graph →
          failure.satisfies (R graph) ∧
            NonTrivialRepairFaithfulness graph (R graph) := by
  intro h
  rcases h with ⟨R, hcollapse, hrepair⟩
  rcases hcollapse monotonicityProbeGraph with ⟨d, hd⟩
  have hfaith :
      NonTrivialRepairFaithfulness monotonicityProbeGraph
        (R monotonicityProbeGraph) :=
    (hrepair monotonicityProbeGraph .monotonicity_violation
      monotonicityProbeGraph_detects_failure).2
  apply hfaith.not_behaviorally_collapse
  refine ⟨d, ?_⟩
  intro claims claimant
  rw [hd]
  simp [claimantConstGraph, graphDecide]
  cases d claimant <;> rfl
/-- Strict faithfulness preserves every external decision while retaining the nontrivial witness condition. This is stronger than `NonTrivialRepairFaithfulness`, whose witness slices permit changing behavior; exact preservation is impossible for universal repair because the failure axioms are extensional in `graphDecide`. -/
def StrictDecisionPreservationFaithfulness (graph repaired : GovernanceGraph) : Prop :=
  NonTrivialRepairFaithfulness graph repaired ∧ GovernanceGraphEquivalent graph repaired
/-- Strict decision-preservation faithfulness contains the nontrivial faithfulness predicate as its first component. The theorem is the projection used to compare the stronger exact-preservation obstruction with the weaker positive repair theorem. -/
theorem strictDecisionPreservationFaithfulness_implies_nontrivial
    {graph repaired : GovernanceGraph} :
    StrictDecisionPreservationFaithfulness graph repaired →
      NonTrivialRepairFaithfulness graph repaired :=
  And.left
/-- Nontrivial faithfulness is strictly weaker than exact decision preservation. The monotonicity probe's non-collapsed replacement is faithful in the scoped sense, but if it were decision-equivalent to the original graph then the repaired monotonicity proof would transfer back and contradict the detected failure. This separates the positive repair witness from the stronger impossibility theorem. -/
theorem nontrivialRepairFaithfulness_not_implies_strictDecisionPreservationFaithfulness :
    ∃ graph repaired : GovernanceGraph, NonTrivialRepairFaithfulness graph repaired ∧
      ¬ StrictDecisionPreservationFaithfulness graph repaired := by
  let repaired := nonCollapsedReplacementRepair monotonicityProbeGraph .monotonicity_violation
  refine ⟨monotonicityProbeGraph, repaired, ?_, ?_⟩
  · exact nonCollapsedReplacementRepair_faithful_of_detected
      monotonicityProbeGraph .monotonicity_violation
      monotonicityProbeGraph_detects_failure
  · intro hstrict
    have hrepaired : GraphMonotonicity repaired := by
      exact nonCollapsedReplacementRepair_satisfies monotonicityProbeGraph
        .monotonicity_violation .monotonicity_violation
    exact monotonicityProbeGraph_detects_failure
      ((graphMonotonicity_congr hstrict.2).mpr hrepaired)
/-- No universal repair can close detected failures while preserving strict decision behavior. The concrete witness is `consistencyProbeGraph` with `consistency_violation`: exact preservation transfers repaired consistency back to the original, contradicting detection. Thus the positive theorem below is tight only at the weaker non-collapsed witness predicate. -/
theorem no_universal_repair_preserves_strict_decision_preservation :
    ¬ ∃ R : GovernanceGraph → AxiomFailureKind → GovernanceGraph,
      ∀ (graph : GovernanceGraph) (failure : AxiomFailureKind),
        failure.detected graph →
          failure.satisfies (R graph failure) ∧
            StrictDecisionPreservationFaithfulness graph (R graph failure) := by
  rintro ⟨R, hrepair⟩
  have hclosed :=
    hrepair consistencyProbeGraph .consistency_violation
      consistencyProbeGraph_detects_failure
  have hrepaired : GraphConsistency (R consistencyProbeGraph .consistency_violation) := hclosed.1
  exact consistencyProbeGraph_detects_failure
    ((graphConsistency_congr hclosed.2.2).mpr hrepaired)
/-- Universal repair exists at the nontrivial-faithfulness level. The repair function is the non-collapsed replacement constructor, and for every detected failure it returns a graph satisfying the failed axiom together with the scoped faithfulness witness. This is the positive counterpart to the strict decision-preservation no-go: it guarantees substantive repair without claiming external decision equivalence. -/
theorem nonCollapsedReplacementRepair_universal_under_nontrivial_faithfulness :
    ∃ R : GovernanceGraph → AxiomFailureKind → GovernanceGraph,
      ∀ (graph : GovernanceGraph) (failure : AxiomFailureKind),
        failure.detected graph →
          failure.satisfies (R graph failure) ∧
            NonTrivialRepairFaithfulness graph (R graph failure) := by
  refine ⟨nonCollapsedReplacementRepair, ?_⟩
  intro graph failure hdetected
  exact ⟨nonCollapsedReplacementRepair_satisfies graph failure failure,
    nonCollapsedReplacementRepair_faithful_of_detected graph failure hdetected⟩
end Legitimacy
