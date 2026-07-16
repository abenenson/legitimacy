/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Impossibility.AxiomIndependence

/-!
# Legitimacy.Impossibility.AxiomLattice

This module packages the order-theoretic classification of the four binary
graph-diagnostic axioms:

* consistency (`C`)
* solidarity (`S`)
* monotonicity (`M`)
* strategyproofness (`SP`)

For conjunctions of these predicates, the only nontrivial implication is
`S ∧ M → SP`. Every other valid implication is just weakening by conjunction.

## Hasse-diagram support table

| Consequent | Nontrivial support |
| --- | --- |
| `C` | none; `exists_non_consistent_solid_monotone_strategyproof` |
| `S` | none; `exists_non_solidarity_consistent_monotone_strategyproof` |
| `M` | none; `exists_non_monotonicity_consistent_solid_strategyproof` |
| `SP` | exactly `S ∧ M`; `solidarity_monotonicity_imply_strategyproof`,
  `exists_non_strategyproof_consistent_monotone`, and
  `exists_non_strategyproof_consistent_solid` |
-/

set_option autoImplicit false

namespace Legitimacy

/-- A boolean mask for conjunctions of the four graph-diagnostic axioms. -/
structure DiagnosticAxiomMask where
  consistency : Bool
  solidarity : Bool
  monotonicity : Bool
  strategyproofness : Bool
  deriving DecidableEq, Repr

namespace DiagnosticAxiomMask

/-- A graph satisfies a mask when it satisfies every axiom whose bit is set. -/
def Holds (m : DiagnosticAxiomMask) (G : GovernanceGraph) : Prop :=
  (m.consistency = true → GraphConsistency G) ∧
    (m.solidarity = true → GraphSolidarity G) ∧
    (m.monotonicity = true → GraphMonotonicity G) ∧
    (m.strategyproofness = true → GraphStrategyproofness G)

/-- Implication between axiom masks, read as implication between conjunctions. -/
def Implies (premise conclusion : DiagnosticAxiomMask) : Prop :=
  ∀ G : GovernanceGraph, Holds premise G → Holds conclusion G

end DiagnosticAxiomMask

/-- Strategyproofness follows from solidarity and monotonicity. -/
theorem strategyproofness_follows_from_solidarity_monotonicity
    {G : GovernanceGraph}
    (hsol : GraphSolidarity G) (hmon : GraphMonotonicity G) :
    GraphStrategyproofness G :=
  solidarity_monotonicity_imply_strategyproof hsol hmon

/-- Consistency is independent of solidarity, monotonicity, and
strategyproofness. -/
theorem consistency_independent_of_solidarity_monotonicity_strategyproofness :
    ∃ G : GovernanceGraph,
      GraphSolidarity G ∧ GraphMonotonicity G ∧ GraphStrategyproofness G ∧
        ¬ GraphConsistency G :=
  exists_non_consistent_solid_monotone_strategyproof

/-- Solidarity is independent of consistency, monotonicity, and
strategyproofness. -/
theorem solidarity_independent_of_consistency_monotonicity_strategyproofness :
    ∃ G : GovernanceGraph,
      GraphConsistency G ∧ GraphMonotonicity G ∧ GraphStrategyproofness G ∧
        ¬ GraphSolidarity G :=
  exists_non_solidarity_consistent_monotone_strategyproof

/-- Monotonicity is independent of consistency, solidarity, and
strategyproofness. -/
theorem monotonicity_independent_of_consistency_solidarity_strategyproofness :
    ∃ G : GovernanceGraph,
      GraphConsistency G ∧ GraphSolidarity G ∧ GraphStrategyproofness G ∧
        ¬ GraphMonotonicity G :=
  exists_non_monotonicity_consistent_solid_strategyproof

/-- Strategyproofness is independent of consistency and monotonicity without
solidarity. -/
theorem strategyproofness_independent_of_consistency_monotonicity :
    ∃ G : GovernanceGraph,
      GraphConsistency G ∧ GraphMonotonicity G ∧ ¬ GraphStrategyproofness G :=
  exists_non_strategyproof_consistent_monotone

/-- Strategyproofness is independent of consistency and solidarity without
monotonicity. -/
theorem strategyproofness_independent_of_consistency_solidarity :
    ∃ G : GovernanceGraph,
      GraphConsistency G ∧ GraphSolidarity G ∧ ¬ GraphStrategyproofness G :=
  exists_non_strategyproof_consistent_solid

/-- Complete mask classification. An implication between conjunctions of the
four graph-diagnostic axioms is valid exactly when each requested consequent
diagnostic is either already present in the premise, or is strategyproofness derived
from the joint premise `solidarity ∧ monotonicity`. -/
theorem diagnostic_axioms_mask_only_nontrivial_implication
    (premise conclusion : DiagnosticAxiomMask) :
    DiagnosticAxiomMask.Implies premise conclusion ↔
      (conclusion.consistency = true → premise.consistency = true) ∧
        (conclusion.solidarity = true → premise.solidarity = true) ∧
        (conclusion.monotonicity = true → premise.monotonicity = true) ∧
        (conclusion.strategyproofness = true →
          premise.strategyproofness = true ∨
            (premise.solidarity = true ∧ premise.monotonicity = true)) := by
  constructor
  · intro himpl
    constructor
    · intro hconclusion
      cases hpremise : premise.consistency
      · rcases exists_non_consistent_solid_monotone_strategyproof with
          ⟨G, hsol, hmon, hsp, hncons⟩
        have hholds : DiagnosticAxiomMask.Holds premise G := by
          simp [DiagnosticAxiomMask.Holds, hpremise, hsol, hmon, hsp]
        exact False.elim (hncons ((himpl G hholds).1 hconclusion))
      · rfl
    constructor
    · intro hconclusion
      cases hpremise : premise.solidarity
      · rcases exists_non_solidarity_consistent_monotone_strategyproof with
          ⟨G, hcons, hmon, hsp, hnsol⟩
        have hholds : DiagnosticAxiomMask.Holds premise G := by
          simp [DiagnosticAxiomMask.Holds, hpremise, hcons, hmon, hsp]
        exact False.elim (hnsol ((himpl G hholds).2.1 hconclusion))
      · rfl
    constructor
    · intro hconclusion
      cases hpremise : premise.monotonicity
      · rcases exists_non_monotonicity_consistent_solid_strategyproof with
          ⟨G, hcons, hsol, hsp, hnmon⟩
        have hholds : DiagnosticAxiomMask.Holds premise G := by
          simp [DiagnosticAxiomMask.Holds, hpremise, hcons, hsol, hsp]
        exact False.elim (hnmon ((himpl G hholds).2.2.1 hconclusion))
      · rfl
    · intro hconclusion
      cases hspPremise : premise.strategyproofness
      · cases hsolPremise : premise.solidarity
        · rcases exists_non_strategyproof_consistent_monotone with
            ⟨G, hcons, hmon, hnsp⟩
          have hholds : DiagnosticAxiomMask.Holds premise G := by
            simp [DiagnosticAxiomMask.Holds, hspPremise, hsolPremise, hcons, hmon]
          exact False.elim (hnsp ((himpl G hholds).2.2.2 hconclusion))
        · cases hmonPremise : premise.monotonicity
          · rcases exists_non_strategyproof_consistent_solid with
              ⟨G, hcons, hsol, hnsp⟩
            have hholds : DiagnosticAxiomMask.Holds premise G := by
              simp [DiagnosticAxiomMask.Holds, hspPremise, hmonPremise, hcons, hsol]
            exact False.elim (hnsp ((himpl G hholds).2.2.2 hconclusion))
          · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl rfl
  · rintro ⟨hconsAllowed, hsolAllowed, hmonAllowed, hspAllowed⟩ G hholds
    constructor
    · intro hconclusion
      exact hholds.1 (hconsAllowed hconclusion)
    constructor
    · intro hconclusion
      exact hholds.2.1 (hsolAllowed hconclusion)
    constructor
    · intro hconclusion
      exact hholds.2.2.1 (hmonAllowed hconclusion)
    · intro hconclusion
      rcases hspAllowed hconclusion with hspPremise | ⟨hsolPremise, hmonPremise⟩
      · exact hholds.2.2.2 hspPremise
      · exact solidarity_monotonicity_imply_strategyproof
          (hholds.2.1 hsolPremise) (hholds.2.2.1 hmonPremise)

end Legitimacy
