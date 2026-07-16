/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.ASIBridge.Native
import Legitimacy.Spectral.CrossScale.FiniteCrossScaleUniversality.FiveNode
import Legitimacy.Spectral.CrossScale.FiniteCrossScaleUniversality.SevenNode
import Legitimacy.Spectral.CrossScale.FiniteCrossScaleUniversality.NineNode

/-!
# Complete-Carrier Specializations of the Native ASI Bridge

This module connects the concrete `uniK5`, `uniK7`, and `uniK9` complete
archetypes to the generic `ASIBridge.asiCompleteGraph` carrier. The spectral
gap corollaries below route the finite certificates through the general
complete-carrier theorem rather than treating the complete rows as independent
table entries.
-/

set_option autoImplicit false

namespace Legitimacy

open Matrix BigOperators

namespace GraphN

/-- Two weighted graph records are equal when their weight matrices are equal.
The proof fields are propositions, so they are discharged by proof
irrelevance after the matrix equality is exposed. -/
theorem weights_ext
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {n : Nat} {G H : GraphN F n} (h : G.weights = H.weights) :
    G = H := by
  cases G
  cases H
  cases h
  simp

end GraphN

/-- The literal five-node complete archetype is the native ASI complete
carrier at successor index `4`. -/
theorem uniK5_eq_asiCompleteGraph :
    uniK5 = ASIBridge.asiCompleteGraph 4 := by
  apply GraphN.weights_ext
  funext i j
  fin_cases i <;> fin_cases j <;> native_decide

/-- The literal seven-node complete archetype is the native ASI complete
carrier at successor index `6`. -/
theorem uniK7_eq_asiCompleteGraph :
    uniK7 = ASIBridge.asiCompleteGraph 6 := by
  apply GraphN.weights_ext
  funext i j
  fin_cases i <;> fin_cases j <;> native_decide

/-- The lambda-defined nine-node complete archetype is the native ASI complete
carrier at successor index `8`. -/
theorem uniK9_eq_asiCompleteGraph :
    uniK9 = ASIBridge.asiCompleteGraph 8 := by
  apply GraphN.weights_ext
  rfl

/-- The concrete five-node rank signal is the native ASI rank signal at
successor index `4`. -/
theorem sig5_eq_asiRankSignal :
    sig5 = ASIBridge.asiRankSignal 4 := by
  funext i
  fin_cases i <;> native_decide

/-- The concrete seven-node rank signal is the native ASI rank signal at
successor index `6`. -/
theorem sig7_eq_asiRankSignal :
    sig7 = ASIBridge.asiRankSignal 6 := by
  funext i
  fin_cases i <;> native_decide

/-- The concrete nine-node rank signal is the native ASI rank signal at
successor index `8`. -/
theorem sig9_eq_asiRankSignal :
    sig9 = ASIBridge.asiRankSignal 8 := by
  funext i
  fin_cases i <;> native_decide

/-- The five-node complete spectral-gap certificate as a specialization of the
general native ASI complete-carrier theorem. -/
theorem uniK5_spectralGap_eq_certificate_via_general :
    uniK5.spectralGap (by norm_num : 2 ≤ 5) =
      (fiveNodeCompleteSpectralGapCertificate : ℝ) := by
  rw [uniK5_eq_asiCompleteGraph]
  have h :=
    ASIBridge.asiCompleteGraph_spectralGap_eq 4 (by norm_num : 2 ≤ 4 + 1)
  norm_num [fiveNodeCompleteSpectralGapCertificate] at h ⊢
  exact h

/-- The seven-node complete spectral-gap certificate as a specialization of the
general native ASI complete-carrier theorem. -/
theorem uniK7_spectralGap_eq_certificate_via_general :
    uniK7.spectralGap (by norm_num : 2 ≤ 7) =
      (sevenNodeCompleteSpectralGapCertificate : ℝ) := by
  rw [uniK7_eq_asiCompleteGraph]
  have h :=
    ASIBridge.asiCompleteGraph_spectralGap_eq 6 (by norm_num : 2 ≤ 6 + 1)
  norm_num [sevenNodeCompleteSpectralGapCertificate] at h ⊢
  exact h

/-- The nine-node complete spectral-gap certificate as a specialization of the
general native ASI complete-carrier theorem. -/
theorem uniK9_spectralGap_eq_certificate_via_general :
    uniK9.spectralGap (by norm_num : 2 ≤ 9) =
      (uniK9SpectralGapCertificate : ℝ) := by
  rw [uniK9_eq_asiCompleteGraph]
  have h :=
    ASIBridge.asiCompleteGraph_spectralGap_eq 8 (by norm_num : 2 ≤ 8 + 1)
  norm_num [uniK9SpectralGapCertificate] at h ⊢
  exact h

end Legitimacy
