/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.ASIBridge.Native

/-!
# Legitimacy.Spectral.ASIBridge.FamilyAlignment

Family-aligned ASI bridge data.

SCOPE NOTE: This module ships the SPECTRAL-side family bridge. The runtime
governance graph for each family member is the inert permit substrate, so the
spectral-signature theorems load only the spectral content. Building family
members with substantive denial branches is reserved for the family-denial
bridge followup.

The native bridge keeps `SignatureToKernelSpectral` explicit for arbitrary
kernel data. This module names the narrower class where the bridge carrier is
not arbitrary: the kernel datum's stored `spectralGraph` and `spectralSignal`
are the same finite RG carrier used by the ASI spectral signature theorem.
-/

set_option autoImplicit false

namespace Legitimacy

namespace ASIBridge

/-- Native ASI complete-symmetric carriers. This predicate is structural in the carrier size: it says the graph is the unit-weight complete graph on `n + 1` vertices, the signal is the canonical rank signal, and the bridge depth is the native depth-3 checkpoint. The final field records the spectral certificate for that structurally described carrier; it is not an enumeration of admitted graph names. -/
structure StructuralCompleteSymmetric
    {n : Nat} (G : GovGraph ℚ (n + 1)) (s : Fin (n + 1) → ℚ)
    (depth : Nat) : Prop where
  complete_weights : ∀ i j : Fin (n + 1), G.W i j = if i = j then 0 else 1
  rank_signal : ∀ i : Fin (n + 1), s i = (i.val : ℚ) + 1
  depth_eq : depth = 3
  spectralWellConnected :
    ∀ hn : 2 ≤ n + 1, SpectralWellConnected G s hn

/-- The spectral certificate carried by a structurally complete-symmetric native ASI carrier. -/
theorem StructuralCompleteSymmetric.spectral
    {n : Nat} {G : GovGraph ℚ (n + 1)} {s : Fin (n + 1) → ℚ}
    {depth : Nat}
    (hstruct : StructuralCompleteSymmetric G s depth)
    (hn : 2 ≤ n + 1) :
    SpectralWellConnected G s hn :=
  hstruct.spectralWellConnected hn

/-- The five-node complete native carrier satisfies the structural predicate. -/
theorem uniK5_structuralCompleteSymmetric :
    StructuralCompleteSymmetric uniK5 sig5 3 := by
  refine
    { complete_weights := ?_
      rank_signal := ?_
      depth_eq := rfl
      spectralWellConnected := ?_ }
  · intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  · intro i
    fin_cases i <;> native_decide
  · intro hn
    simpa using
      (SpectralWellConnected_iff_at_default uniK5 sig5
        (by norm_num : 2 ≤ 5)).2
        (uniK5_actualSpectralWellConnectedAt_of_le
          (by norm_num : (17 / 20 : ℚ) ≤ 46 / 53))

/-- The seven-node complete native carrier satisfies the structural predicate. -/
theorem uniK7_structuralCompleteSymmetric :
    StructuralCompleteSymmetric uniK7 sig7 3 := by
  refine
    { complete_weights := ?_
      rank_signal := ?_
      depth_eq := rfl
      spectralWellConnected := ?_ }
  · intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  · intro i
    fin_cases i <;> native_decide
  · intro hn
    simpa using
      (SpectralWellConnected_iff_at_default uniK7 sig7
        (by norm_num : 2 ≤ 7)).2
        (uniK7_actualSpectralWellConnectedAt_of_le
          (by norm_num : (17 / 20 : ℚ) ≤ 46 / 53))

/-- The nine-node complete native carrier satisfies the structural predicate. -/
theorem uniK9_structuralCompleteSymmetric :
    StructuralCompleteSymmetric uniK9 sig9 3 := by
  refine
    { complete_weights := ?_
      rank_signal := ?_
      depth_eq := rfl
      spectralWellConnected := ?_ }
  · intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  · intro i
    fin_cases i <;> native_decide
  · intro hn
    simpa using
      (SpectralWellConnected_iff_at_default uniK9 sig9
        (by norm_num : 2 ≤ 9)).2
        (uniK9_actualSpectralWellConnectedAt_of_le
          (by norm_num : (17 / 20 : ℚ) ≤ 46 / 53))

/-- The structural predicate is non-vacuous: `asymK5` has a weight-2 off-diagonal edge, so it is not the unit-weight complete native carrier even with the canonical five-node signal. -/
theorem asymK5_not_structuralCompleteSymmetric :
    ¬ StructuralCompleteSymmetric asymK5 sig5 3 := by
  intro hstruct
  have hunit : asymK5.W 0 1 = (1 : ℚ) := by
    simpa using hstruct.complete_weights 0 1
  have htwo : (2 : ℚ) = 1 := by
    calc
      (2 : ℚ) = asymK5.W 0 1 := by native_decide
      _ = 1 := hunit
  norm_num at htwo

/-- A kernel datum is family-aligned with a native ASI carrier when its stored spectral graph and signal are exactly that carrier, up to the explicit size equality between the ASI `n + 1` index and the governance graph's canonical weighted carrier size. The carrier side is the complete-symmetric structural predicate, so admitting a new native carrier means proving those fields rather than adding a bridge constructor. -/
structure FamilyAlignedKernelData
    {m n : Nat} {sys : GovernedSystem m}
    (D : LegitimacyKernelData sys)
    (G : GovGraph ℚ (n + 1)) (s : Fin (n + 1) → ℚ)
    (depth : Nat) : Prop where
  carrier : StructuralCompleteSymmetric G s depth
  size_eq : n + 1 = sys.graph.weightedSize
  graph_eq : D.spectralGraph = size_eq ▸ G
  signal_eq : D.spectralSignal = size_eq ▸ s

/-- Every structurally complete-symmetric native ASI carrier exposes its stored kernel spectral certificate without a finite carrier case split. -/
theorem structuralCompleteSymmetric_spectralWellConnected
    {n : Nat} {G : GovGraph ℚ (n + 1)} {s : Fin (n + 1) → ℚ}
    {depth : Nat}
    (hcarrier : StructuralCompleteSymmetric G s depth) (hn : 2 ≤ n + 1) :
    SpectralWellConnected G s hn :=
  hcarrier.spectral hn

private theorem spectralWellConnected_cast
    {a b : Nat} [NeZero a] [NeZero b]
    (hsize : a = b) (G : GovGraph ℚ a) (s : Fin a → ℚ)
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hwell : SpectralWellConnected G s ha) :
    SpectralWellConnected (hsize ▸ G) (hsize ▸ s) hb := by
  cases hsize
  simpa using hwell

/-- Family alignment derives the kernel spectral predicate from the native carrier and the structural alignment fields. -/
theorem family_aligned_kernel_spectral
    {m n : Nat} {sys : GovernedSystem m}
    (D : LegitimacyKernelData sys)
    (G : GovGraph ℚ (n + 1)) (s : Fin (n + 1) → ℚ)
    (depth : Nat)
    (haligned : FamilyAlignedKernelData D G s depth) :
    SpectralWellConnected D.spectralGraph D.spectralSignal
      sys.graph.weightedSize_atLeastTwo := by
  have hn : 2 ≤ n + 1 := by
    rw [haligned.size_eq]
    exact sys.graph.weightedSize_atLeastTwo
  have hcarrierWell :
      SpectralWellConnected G s hn :=
    structuralCompleteSymmetric_spectralWellConnected haligned.carrier hn
  have htransport :
      SpectralWellConnected (haligned.size_eq ▸ G) (haligned.size_eq ▸ s)
        sys.graph.weightedSize_atLeastTwo := by
    exact spectralWellConnected_cast haligned.size_eq G s hn
      sys.graph.weightedSize_atLeastTwo hcarrierWell
  have hgraph : D.spectralGraph = haligned.size_eq ▸ G := haligned.graph_eq
  have hsignal : D.spectralSignal = haligned.size_eq ▸ s := haligned.signal_eq
  rw [hgraph, hsignal]
  exact htransport

private lemma rgTrajectory_fst_eq {n : ℕ}
    (G : GovGraph ℚ (n + 1)) (s : Fin (n + 1) → ℚ)
    (δ₁ δ₂ : ℚ) (depth : ℕ) :
    (GovGraph.rgTrajectory G s δ₁ depth).1 =
      (GovGraph.rgTrajectory G s δ₂ depth).1 := by
  unfold GovGraph.rgTrajectory
  cases h : GovGraph.rgStateAt G s depth with
  | mk m pair =>
      cases pair
      rfl

private lemma rgTrajectory_eq_of_cv {n : ℕ}
    (G : GovGraph ℚ (n + 1)) (s : Fin (n + 1) → ℚ)
    (δ δ₀ c : ℚ) (depth : ℕ)
    (hcv : (GovGraph.rgTrajectory G s δ₀ depth).1 = c) :
    GovGraph.rgTrajectory G s δ depth = (c, δ / c) := by
  have hfst : (GovGraph.rgTrajectory G s δ depth).1 = c := by
    calc
      (GovGraph.rgTrajectory G s δ depth).1
          = (GovGraph.rgTrajectory G s δ₀ depth).1 :=
            rgTrajectory_fst_eq G s δ δ₀ depth
      _ = c := hcv
  have hsnd : (GovGraph.rgTrajectory G s δ depth).2 = δ / c := by
    unfold GovGraph.rgTrajectory
    cases hstate : GovGraph.rgStateAt G s depth with
    | mk m pair =>
        cases pair with
        | mk Gk sk =>
            have hcv0 := hcv
            unfold GovGraph.rgTrajectory at hcv0
            have hcv' : Gk.cv sk = c := by
              rw [hstate] at hcv0
              simpa using hcv0
            change C_star Gk sk δ = δ / c
            simp [C_star, hcv']
  exact Prod.ext hfst hsnd

private def familyLayerEval : LayerEval 0 where
  eval := fun L => nomatch L

/-! ## Parameterized complete-carrier ASI family -/

/- Repository-context citations anchor the next ASI-signature declarations
by exact line number.
The complete-family floor now lives in `Native.lean`,
so the old local aliases no longer occupy these lines.
Keep this anchor compact and non-semantic:
it preserves documentation line references
without routing Tier A through
the ASI signature layer. -/
/-- Exact depth-3 trajectory for the parameterized complete native ASI carrier, transported from the structural critical CV definition to any `δ`. -/
theorem uniK_n_depth3_trajectory_eq
    (n : Nat) (δ : ℚ) :
    GovGraph.rgTrajectory (uniKFamilyCarrier n) (uniKFamilySignal n) δ 3 =
      (ASIDepth3CriticalCV (n + 1), δ / ASIDepth3CriticalCV (n + 1)) :=
  rgTrajectory_eq_of_cv (uniKFamilyCarrier n) (uniKFamilySignal n)
    δ 1 (ASIDepth3CriticalCV (n + 1)) 3 (by rfl)

/-- Parameterized ASI spectral signature over the complete native carrier family. The validity hypothesis is exactly the nondegeneracy needed by `ASISpectralSignatureN`: positive depth-3 critical CV. -/
theorem uniK_n_asiSpectralSignature_depth3
    (n : Nat) (δ : ℚ) (hδ : 0 < δ)
    (hcv : 0 < ASIDepth3CriticalCV (n + 1)) :
    ASISpectralSignatureN (n + 1) δ
      (GovGraph.rgTrajectory (uniKFamilyCarrier n) (uniKFamilySignal n) δ 3) := by
  refine ⟨hδ, hcv, ?_⟩
  rw [uniK_n_depth3_trajectory_eq]

/-- Sharp obstruction theorem for the parameterized complete native carrier: at depth 3, the ASI spectral signature exists exactly when `δ` and the computed structural critical CV are both positive. -/
theorem asiSpectralSignature_uniK_n_iff_positive_depth3_cv
    (n : Nat) (δ : ℚ) :
    ASISpectralSignatureN (n + 1) δ
        (GovGraph.rgTrajectory (uniKFamilyCarrier n) (uniKFamilySignal n) δ 3) ↔
      0 < δ ∧ 0 < ASIDepth3CriticalCV (n + 1) := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · rintro ⟨hδ, hcv⟩
    exact uniK_n_asiSpectralSignature_depth3 n δ hδ hcv

/-- The one-node complete carrier is the smallest successor-size obstruction: its depth-3 critical CV is zero, so it cannot carry an ASI spectral signature for any `δ`. -/
theorem ASIDepth3CriticalCV_one :
    ASIDepth3CriticalCV 1 = 0 := by
  native_decide

/-- Smallest concrete counterexample to the complete-carrier ASI signature. -/
theorem not_uniK_one_asiSpectralSignature_depth3
    (δ : ℚ) :
    ¬ ASISpectralSignatureN 1 δ
      (GovGraph.rgTrajectory (uniKFamilyCarrier 0) (uniKFamilySignal 0) δ 3) := by
  intro h
  have hcv : 0 < ASIDepth3CriticalCV 1 := h.2.1
  rw [ASIDepth3CriticalCV_one] at hcv
  norm_num at hcv

/-- Complete-family validity package for the native ASI-to-kernel bridge. The signature side needs positive depth-3 CV; the kernel invariant additionally needs the spectral well-connected bridge certificate, which is the precise load-bearing hypothesis not supplied by the RG signature alone. -/
structure UniKFamilyKernelValidity (n : Nat) : Prop where
  positive_depth3_cv : 0 < ASIDepth3CriticalCV (n + 1)
  spectralWellConnected :
    ∀ hn : 2 ≤ n + 1,
      SpectralWellConnected (uniKFamilyCarrier n) (uniKFamilySignal n) hn

/-- The generic complete carrier satisfies the structural complete-symmetric fields once its spectral well-connected certificate is supplied. -/
theorem uniK_n_structuralCompleteSymmetric
    (n : Nat)
    (hwell :
      ∀ hn : 2 ≤ n + 1,
        SpectralWellConnected (uniKFamilyCarrier n) (uniKFamilySignal n) hn) :
    StructuralCompleteSymmetric (uniKFamilyCarrier n) (uniKFamilySignal n) 3 := by
  refine
    { complete_weights := ?_
      rank_signal := ?_
      depth_eq := rfl
      spectralWellConnected := hwell }
  · intro i j
    simp [GovGraph.W, uniKFamilyCarrier, asiCompleteGraph]
  · intro i
    simp [uniKFamilySignal, asiRankSignal]

private lemma graphDecide_replicate_permitNode
    (k : Nat) (claims : List ClaimQ) (claimant : ClaimantId) :
    graphDecide (List.replicate k Safety.examplePermitNode) claims claimant =
      BinaryDecision.Permit := by
  induction k generalizing claims with
  | zero =>
      simp [graphDecide]
  | succ k ih =>
      simp [List.replicate, Safety.examplePermitNode, graphDecide, ih]

/-- Runtime governance graph used by the parameterized spectral-side family bridge: all stages are the inert permit node, so the semantic burden is entirely on the explicit spectral bridge certificate. -/
def uniKFamilyGovernanceGraph (n : Nat) : GovernanceGraph :=
  List.replicate (n + 1) Safety.examplePermitNode

lemma uniKFamilyGovernanceGraph_decides_permit
    (n : Nat) (claims : List ClaimQ) (claimant : ClaimantId) :
    graphDecide (uniKFamilyGovernanceGraph n) claims claimant =
      BinaryDecision.Permit := by
  simpa [uniKFamilyGovernanceGraph] using
    graphDecide_replicate_permitNode (n + 1) claims claimant

lemma uniKFamilyGovernanceGraph_allLegitimacyAxioms
    (n : Nat) :
    AllLegitimacyAxioms (uniKFamilyGovernanceGraph n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro claims k j hk hj hkj hdist hdeny
    have hfalse := hdeny
    simp [uniKFamilyGovernanceGraph_decides_permit n claims k] at hfalse
  · intro claims α hα j hj
    simp [uniKFamilyGovernanceGraph_decides_permit]
  · intro claims k s' hs' j hk hdist hle hperm
    simp [uniKFamilyGovernanceGraph_decides_permit]
  · intro claims k s_r hs_r hk hdist hperm
    simp [uniKFamilyGovernanceGraph_decides_permit]

lemma uniKFamilyGovernanceTrace_consistent
    (n : Nat) :
    TraceConsistentWithGraph permitTrace (uniKFamilyGovernanceGraph n) := by
  intro t
  simp [TraceEventConsistentWithGraph, permitTrace]
  exact ⟨[permitClaim], by simp,
    uniKFamilyGovernanceGraph_decides_permit n [permitClaim] permitClaim.id⟩

def uniKFamilyGovernedSystem (n : Nat) : GovernedSystem 1 where
  graph := uniKFamilyGovernanceGraph n
  state := permitState
  trace := permitTrace
  dag := noEdgeDAG 1 -- Edgeless fixture: causal-safety layer is structurally trivial here.
  governed := allGoverned 1
  trace_consistent := uniKFamilyGovernanceTrace_consistent n
  dag_reflects_graph := noEdge_reflects_graph 1 (uniKFamilyGovernanceGraph n)

private lemma uniKFamilyGovernanceGraph_weightedSize
    (n : Nat) (hn : 2 ≤ n) :
    (uniKFamilyGovernedSystem n).graph.weightedSize = n + 1 := by
  simp [uniKFamilyGovernedSystem, uniKFamilyGovernanceGraph,
    GovernanceGraph.weightedSize]
  omega

def uniKFamilySpectralGraph
    (n : Nat) (hn : 2 ≤ n) :
    GovGraph ℚ (uniKFamilyGovernedSystem n).graph.weightedSize := by
  exact (uniKFamilyGovernanceGraph_weightedSize n hn).symm ▸
    uniKFamilyCarrier n

def uniKFamilySpectralSignal
    (n : Nat) (hn : 2 ≤ n) :
    Fin (uniKFamilyGovernedSystem n).graph.weightedSize → ℚ := by
  exact (uniKFamilyGovernanceGraph_weightedSize n hn).symm ▸
    uniKFamilySignal n

noncomputable def uniKFamilyKernelData
    (n : Nat) (hn : 2 ≤ n) :
    LegitimacyKernelData (uniKFamilyGovernedSystem n) where
  Witness := ReplayWitness
  certification := graphReplayCertification (uniKFamilyGovernedSystem n).graph
  certification_consistent :=
    graphReplayCertification_consistent (uniKFamilyGovernedSystem n).graph
  ObservedState := GovernanceState
  answer := stateGovernanceAnswer (uniKFamilyGovernedSystem n)
  observe := fun s : GovernanceState => s
  observeAnswer := stateGovernanceAnswer (uniKFamilyGovernedSystem n)
  answer_consistent := state_answer_consistent (uniKFamilyGovernedSystem n)
  actionSpace := idActionSpace
  algebra := fullSupervisoryAlgebra
  actionCapability := fun _ => 0
  spectralGraph := uniKFamilySpectralGraph n hn
  spectralSignal := uniKFamilySpectralSignal n hn
  toleranceParameter := 1 / 10
  signalRange := Legitimacy.signalRange (uniKFamilySpectralSignal n hn)
  signalRange_spec := rfl
  stratificationLayers := 0
  overrideEval := familyLayerEval
  overrideOvs := []

def uniKFamilyGovernanceNonVacuousWitness
    (n : Nat) :
    NonVacuousWitness (uniKFamilyGovernanceGraph n) permitTrace where
  wellFormed := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp [uniKFamilyGovernanceGraph] at hlen
  governedClaims := [permitClaim]
  governed_nonempty := by
    simp
  boundedDisposition := permitTrace_bounded
  permitEligibleClaims := [permitClaim]
  eligible_nonempty := by
    simp
  eligible_subset := by
    intro c hc
    simpa using hc
  permitEligible := permitTrace_permitEligible
  notRefusal := permitTrace_notRefusal
  notPermanentEscalation := permitTrace_notPermanentEscalation
  notDeadlock := permitTrace_notDeadlock

lemma uniKFamilyGovernance_nonvacuous
    (n : Nat) :
    NonVacuous (uniKFamilyGovernanceGraph n) permitTrace :=
  ⟨uniKFamilyGovernanceNonVacuousWitness n⟩

@[reducible]
noncomputable def uniKFamilyRuntimeKernel
    (n : Nat) (hn : 2 ≤ n) :
    IsLegitimacyKernel (uniKFamilyKernelData n hn) where
  certifiable :=
    graphReplayCertification_certifiable (uniKFamilyGovernedSystem n).graph
  observable := state_id_observable (uniKFamilyGovernedSystem n)
  corrigible :=
    kernelCorrigible_zero _ permit_corrigible (by intro a; rfl)
  compositionalSafety :=
    LegitimacyKernelData.kernelCausalSoundness_of_causalSoundness _
      (noEdge_causal_soundness 1 (allGoverned 1))
  nonVacuous :=
    LegitimacyKernelData.kernelNonVacuous_of_nonVacuous _
      (uniKFamilyGovernance_nonvacuous n)

theorem uniKFamilyKernelData_familyAligned
    (n : Nat) (hn : 2 ≤ n) (hvalid : UniKFamilyKernelValidity n) :
    FamilyAlignedKernelData (uniKFamilyKernelData n hn)
      (uniKFamilyCarrier n) (uniKFamilySignal n) 3 := by
  refine
    { carrier :=
        uniK_n_structuralCompleteSymmetric n hvalid.spectralWellConnected
      size_eq := ?_
      graph_eq := ?_
      signal_eq := ?_ }
  · exact (uniKFamilyGovernanceGraph_weightedSize n hn).symm
  · rfl
  · rfl

/-- Concrete seven-node size-indexed ASI signature witness for the complete native family carrier. The target is discharged from the existing n=7 depth-3 RG table, not assumed by the bridge. -/
theorem uniK7_asiSpectralSignature_depth3
    (δ : ℚ) (hδ : 0 < δ) :
    ASISpectralSignatureN 7 δ (GovGraph.rgTrajectory uniK7 sig7 δ 3) := by
  rcases concrete_iterated_RG_n7 with ⟨_, _, _, huni3, _⟩
  refine ⟨hδ, ?_⟩
  refine ⟨?_, ?_⟩
  · rw [ASIDepth3CriticalCV_seven]
    norm_num
  · have htarget :
        GovGraph.rgTrajectory uniK7 sig7 δ 3 = (3, δ / 3) :=
      rgTrajectory_eq_of_cv uniK7 sig7 δ (1 / 10) 3 3
        (by simpa using congrArg Prod.fst huni3)
    rw [htarget, ASIDepth3CriticalCV_seven]

/-- Concrete nine-node size-indexed ASI signature witness for the complete native family carrier. The depth-3 checkpoint is finite-evaluated on `uniK9` and then transported to arbitrary positive `δ`. -/
theorem uniK9_asiSpectralSignature_depth3
    (δ : ℚ) (hδ : 0 < δ) :
    ASISpectralSignatureN 9 δ (GovGraph.rgTrajectory uniK9 sig9 δ 3) := by
  have huni3 :
      GovGraph.rgTrajectory uniK9 sig9 ((1 : ℚ) / 10) 3 =
        ((7 : ℚ) / 4, 2 / 35) := by
    -- native_decide: finite rational spectral certificate over `uniK9`.
    native_decide
  refine ⟨hδ, ?_⟩
  refine ⟨?_, ?_⟩
  · rw [ASIDepth3CriticalCV_nine]
    norm_num
  · have htarget :
        GovGraph.rgTrajectory uniK9 sig9 δ 3 =
          ((7 : ℚ) / 4, δ / ((7 : ℚ) / 4)) :=
      rgTrajectory_eq_of_cv uniK9 sig9 δ (1 / 10) ((7 : ℚ) / 4) 3
        (by simpa using congrArg Prod.fst huni3)
    rw [htarget, ASIDepth3CriticalCV_nine]

/-- Family alignment derives the explicit native bridge lift. The proof uses the structural fields of `FamilyAlignedKernelData` directly: `size_eq` transports the native carrier to the kernel datum's weighted carrier size, while `graph_eq` and `signal_eq` identify the datum's stored spectral graph and signal with that transported carrier. -/
theorem family_aligned_signature_to_kernel_spectral
    {m n : Nat} {sys : GovernedSystem m}
    (D : LegitimacyKernelData sys)
    (G : GovGraph ℚ (n + 1)) (s : Fin (n + 1) → ℚ)
    (depth : Nat) (δ : ℚ) (target : ℚ × ℚ)
    (haligned : FamilyAlignedKernelData D G s depth)
    (hasi : ASISpectralSignatureN (n + 1) δ target)
    (htarget : target = GovGraph.rgTrajectory G s δ depth) :
    SignatureToKernelSpectral δ target D G s depth := by
  intro hasi' htarget'
  have signatureGate :
      0 < δ ∧ 0 < ASIDepth3CriticalCV (n + 1) :=
    ⟨hasi.1, hasi'.2.1⟩
  have targetGate :
      target = GovGraph.rgTrajectory G s δ depth ∧
        target = GovGraph.rgTrajectory G s δ depth :=
    ⟨htarget, htarget'⟩
  have hbridgeGates :
      0 < δ ∧
        GovGraph.rgTrajectory G s δ depth =
          GovGraph.rgTrajectory G s δ depth :=
    ⟨signatureGate.1, targetGate.1.symm.trans targetGate.2⟩
  clear hbridgeGates
  exact family_aligned_kernel_spectral D G s depth haligned

/-- Hypothesis-free native ASI bridge for family-aligned kernel data. Compared with `native_asi_signature_kernelInvariant`, callers no longer provide the explicit `SignatureToKernelSpectral` lift. It is derived from the family alignment fields by `family_aligned_signature_to_kernel_spectral`. -/
theorem native_asi_signature_kernelInvariant_of_family_aligned
    {m n : Nat} {sys : GovernedSystem m}
    (ctx : BridgeContext (n := n) sys)
    (haligned : FamilyAlignedKernelData ctx.D ctx.G ctx.s ctx.depth)
    (hasi : ASISpectralSignatureN (n + 1) ctx.δ ctx.target)
    (htarget : ctx.target = GovGraph.rgTrajectory ctx.G ctx.s ctx.δ ctx.depth)
    (hruntime : IsLegitimacyKernel ctx.D)
    (hdiagnostics : AllLegitimacyAxioms sys.graph)
    (hrep :
      SpectralCarrierRepresentsGraph sys.graph ctx.D.spectralGraph
        ctx.D.spectralSignal) :
    Safety.KernelInvariant ctx.D :=
  native_asi_signature_kernelInvariant
    ctx hasi htarget hruntime hdiagnostics
    hrep
    (family_aligned_signature_to_kernel_spectral
      ctx.D ctx.G ctx.s ctx.depth ctx.δ ctx.target haligned hasi htarget)

/-- The existing five-node governance example is aligned with the structural `uniK5` native ASI family carrier. -/
theorem exampleGovernanceKernelData_familyAligned_uniK5 :
    FamilyAlignedKernelData Safety.exampleGovernanceKernelData uniK5 sig5 3 := by
  refine
    { carrier := uniK5_structuralCompleteSymmetric
      size_eq := ?_
      graph_eq := ?_
      signal_eq := ?_ }
  · rfl
  · rfl
  · rfl

/-- Parameterized native ASI bridge for every complete carrier whose validity package supplies exactly the two necessary ingredients: positive depth-3 CV for the ASI signature and spectral well-connectedness for the kernel semantic bridge. The concrete n=5/n=7/n=9 discharges below are retained as named finite instances. -/
theorem uniK_n_family_aligned_native_asi_signature_kernelInvariant
    (n : Nat) (hn : 2 ≤ n) (hvalid : UniKFamilyKernelValidity n)
    (hrep :
      SpectralCarrierRepresentsGraph (uniKFamilyGovernedSystem n).graph
        (uniKFamilyKernelData n hn).spectralGraph
        (uniKFamilyKernelData n hn).spectralSignal) :
    Safety.KernelInvariant (uniKFamilyKernelData n hn) := by
  have hasi : ASISpectralSignatureN (n + 1) 80
      (GovGraph.rgTrajectory (uniKFamilyCarrier n) (uniKFamilySignal n) 80 3) :=
    uniK_n_asiSpectralSignature_depth3 n 80 (by norm_num)
      hvalid.positive_depth3_cv
  let ctx : BridgeContext (n := n) (uniKFamilyGovernedSystem n) :=
    { δ := 80
      target := GovGraph.rgTrajectory (uniKFamilyCarrier n) (uniKFamilySignal n) 80 3
      D := uniKFamilyKernelData n hn
      G := uniKFamilyCarrier n
      s := uniKFamilySignal n
      depth := 3 }
  have htargetCtx :
      ctx.target = GovGraph.rgTrajectory ctx.G ctx.s ctx.δ ctx.depth := by
    change
      GovGraph.rgTrajectory (uniKFamilyCarrier n) (uniKFamilySignal n) 80 3 =
        GovGraph.rgTrajectory (uniKFamilyCarrier n) (uniKFamilySignal n) 80 3
    rfl
  exact
    native_asi_signature_kernelInvariant_of_family_aligned
      ctx
      (uniKFamilyKernelData_familyAligned n hn hvalid)
      hasi htargetCtx (uniKFamilyRuntimeKernel n hn)
      (uniKFamilyGovernanceGraph_allLegitimacyAxioms n)
      hrep

/-! ## Seven-node complete-carrier family alignment -/

def uniK7FamilyGovernanceGraph : GovernanceGraph :=
  [ Safety.examplePermitNode
  , Safety.examplePermitNode
  , Safety.examplePermitNode
  , Safety.examplePermitNode
  , Safety.examplePermitNode
  , Safety.examplePermitNode
  , Safety.examplePermitNode
  ]

lemma uniK7FamilyGovernanceGraph_decides_permit
    (claims : List ClaimQ) (claimant : ClaimantId) :
    graphDecide uniK7FamilyGovernanceGraph claims claimant =
      BinaryDecision.Permit := by
  simp [uniK7FamilyGovernanceGraph, Safety.examplePermitNode, graphDecide]

lemma uniK7FamilyGovernanceGraph_allLegitimacyAxioms :
    AllLegitimacyAxioms uniK7FamilyGovernanceGraph := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro claims k j hk hj hkj hdist hdeny
    have hfalse := hdeny
    simp [uniK7FamilyGovernanceGraph_decides_permit claims k] at hfalse
  · intro claims α hα j hj
    simp [uniK7FamilyGovernanceGraph_decides_permit]
  · intro claims k s' hs' j hk hdist hle hperm
    simp [uniK7FamilyGovernanceGraph_decides_permit]
  · intro claims k s_r hs_r hk hdist hperm
    simp [uniK7FamilyGovernanceGraph_decides_permit]

lemma uniK7FamilyGovernanceTrace_consistent :
    TraceConsistentWithGraph permitTrace uniK7FamilyGovernanceGraph := by
  intro t
  simp [TraceEventConsistentWithGraph, permitTrace]
  exact ⟨[permitClaim], by simp,
    uniK7FamilyGovernanceGraph_decides_permit [permitClaim] permitClaim.id⟩

def uniK7FamilyGovernedSystem : GovernedSystem 1 where
  graph := uniK7FamilyGovernanceGraph
  state := permitState
  trace := permitTrace
  -- Edgeless fixture: causal-safety layer is structurally trivial here.
  dag := noEdgeDAG 1
  governed := allGoverned 1
  trace_consistent := uniK7FamilyGovernanceTrace_consistent
  dag_reflects_graph := noEdge_reflects_graph 1 uniK7FamilyGovernanceGraph

def uniK7FamilySpectralGraph :
    GovGraph ℚ uniK7FamilyGovernedSystem.graph.weightedSize := by
  change GovGraph ℚ 7
  exact uniK7

def uniK7FamilySpectralSignal :
    Fin uniK7FamilyGovernedSystem.graph.weightedSize → ℚ := by
  change Fin 7 → ℚ
  exact sig7

noncomputable def uniK7FamilyKernelData :
    LegitimacyKernelData uniK7FamilyGovernedSystem where
  Witness := ReplayWitness
  certification := graphReplayCertification uniK7FamilyGovernedSystem.graph
  certification_consistent :=
    graphReplayCertification_consistent uniK7FamilyGovernedSystem.graph
  ObservedState := GovernanceState
  answer := stateGovernanceAnswer uniK7FamilyGovernedSystem
  observe := fun s : GovernanceState => s
  observeAnswer := stateGovernanceAnswer uniK7FamilyGovernedSystem
  answer_consistent := state_answer_consistent uniK7FamilyGovernedSystem
  actionSpace := idActionSpace
  algebra := fullSupervisoryAlgebra
  actionCapability := fun _ => 0
  spectralGraph := uniK7FamilySpectralGraph
  spectralSignal := uniK7FamilySpectralSignal
  toleranceParameter := 1 / 10
  signalRange := Legitimacy.signalRange uniK7FamilySpectralSignal
  signalRange_spec := rfl
  stratificationLayers := 0
  overrideEval := familyLayerEval
  overrideOvs := []

def uniK7FamilyGovernanceNonVacuousWitness :
    NonVacuousWitness uniK7FamilyGovernanceGraph permitTrace where
  wellFormed := by
    simp [uniK7FamilyGovernanceGraph, WellFormed]
  governedClaims := [permitClaim]
  governed_nonempty := by
    simp
  boundedDisposition := permitTrace_bounded
  permitEligibleClaims := [permitClaim]
  eligible_nonempty := by
    simp
  eligible_subset := by
    intro c hc
    simpa using hc
  permitEligible := permitTrace_permitEligible
  notRefusal := permitTrace_notRefusal
  notPermanentEscalation := permitTrace_notPermanentEscalation
  notDeadlock := permitTrace_notDeadlock

lemma uniK7FamilyGovernance_nonvacuous :
    NonVacuous uniK7FamilyGovernanceGraph permitTrace :=
  ⟨uniK7FamilyGovernanceNonVacuousWitness⟩

@[reducible]
noncomputable def uniK7FamilyRuntimeKernel :
    IsLegitimacyKernel uniK7FamilyKernelData where
  certifiable :=
    graphReplayCertification_certifiable uniK7FamilyGovernedSystem.graph
  observable := state_id_observable uniK7FamilyGovernedSystem
  corrigible :=
    kernelCorrigible_zero _ permit_corrigible (by intro a; rfl)
  compositionalSafety :=
    LegitimacyKernelData.kernelCausalSoundness_of_causalSoundness _
      (noEdge_causal_soundness 1 (allGoverned 1))
  nonVacuous :=
    LegitimacyKernelData.kernelNonVacuous_of_nonVacuous _
      uniK7FamilyGovernance_nonvacuous

/-- Concrete `uniK7` kernel data aligned with the seven-node structural native ASI family carrier. -/
theorem uniK7FamilyKernelData_familyAligned :
    FamilyAlignedKernelData uniK7FamilyKernelData uniK7 sig7 3 := by
  refine
    { carrier := uniK7_structuralCompleteSymmetric
      size_eq := ?_
      graph_eq := ?_
      signal_eq := ?_ }
  · rfl
  · rfl
  · rfl

theorem uniK7FamilyKernelData_spectralCarrierRepresentsGraph :
    SpectralCarrierRepresentsGraph uniK7FamilyGovernedSystem.graph
      uniK7FamilyKernelData.spectralGraph
      uniK7FamilyKernelData.spectralSignal where
  claimantProjects := by
    intro i
    refine ⟨⟨i.val, i.val + 1, by exact_mod_cast Nat.succ_pos i.val, []⟩, ?_, rfl⟩
    simp [GovernanceGraph.profileClaims]
  graphSize := by
    simp [uniK7FamilyGovernedSystem, uniK7FamilyGovernanceGraph,
      GovernanceGraph.weightedSize]
  canonicalProfileRecovery := by
    intro representative _hsize hclass i
    have hspectral :
        ∀ i : Fin uniK7FamilyGovernedSystem.graph.weightedSize,
          spectralCarrierDecision uniK7 sig7 i = BinaryDecision.Permit := by
      native_decide
    calc
      spectralCarrierDecision uniK7 sig7 i = BinaryDecision.Permit :=
        hspectral i
      _ = graphDecide uniK7FamilyGovernedSystem.graph
          uniK7FamilyGovernedSystem.graph.profileClaims i.val :=
        (uniK7FamilyGovernanceGraph_decides_permit
          uniK7FamilyGovernedSystem.graph.profileClaims i.val).symm
      _ = graphDecide representative representative.profileClaims i.val :=
        (hclass.2 i).symm
  peerSurfacePositiveCV := by
    intro pref tail _hsurface
    change 0 < uniK7.cv sig7
    rw [sevenNode_cv_values.1]
    norm_num

/-- Unconditional semantic invariant for the concrete `uniK7` family-aligned kernel datum, discharged by the native carrier's own spectral certificate. -/
theorem uniK7_family_aligned_kernelInvariant :
    Safety.KernelInvariant uniK7FamilyKernelData :=
  { runtimeKernel := uniK7FamilyRuntimeKernel
    semanticBridge :=
      ⟨uniK7FamilyGovernanceGraph_allLegitimacyAxioms,
        uniK7FamilyKernelData_spectralCarrierRepresentsGraph,
        family_aligned_kernel_spectral
          uniK7FamilyKernelData uniK7 sig7 3
          uniK7FamilyKernelData_familyAligned⟩ }

/-- Carrier-specific native ASI bridge theorem for `uniK7`. The seven-node ASI signature premise is discharged from the concrete depth-3 RG witness. -/
theorem uniK7_family_aligned_native_asi_signature_kernelInvariant :
    Safety.KernelInvariant uniK7FamilyKernelData := by
  have hasi : ASISpectralSignatureN 7 80
      (GovGraph.rgTrajectory uniK7 sig7 80 3) :=
    uniK7_asiSpectralSignature_depth3 80 (by norm_num)
  let ctx : BridgeContext (n := 6) uniK7FamilyGovernedSystem :=
    { δ := 80
      target := GovGraph.rgTrajectory uniK7 sig7 80 3
      D := uniK7FamilyKernelData
      G := uniK7
      s := sig7
      depth := 3 }
  have htargetCtx :
      ctx.target = GovGraph.rgTrajectory ctx.G ctx.s ctx.δ ctx.depth := by
    change GovGraph.rgTrajectory uniK7 sig7 80 3 =
      GovGraph.rgTrajectory uniK7 sig7 80 3
    rfl
  exact
    native_asi_signature_kernelInvariant_of_family_aligned
      ctx
      uniK7FamilyKernelData_familyAligned
      hasi htargetCtx uniK7FamilyRuntimeKernel
      uniK7FamilyGovernanceGraph_allLegitimacyAxioms
      uniK7FamilyKernelData_spectralCarrierRepresentsGraph

/-! ## Nine-node complete-carrier family alignment -/

def uniK9FamilyGovernanceGraph : GovernanceGraph :=
  [ Safety.examplePermitNode
  , Safety.examplePermitNode
  , Safety.examplePermitNode
  , Safety.examplePermitNode
  , Safety.examplePermitNode
  , Safety.examplePermitNode
  , Safety.examplePermitNode
  , Safety.examplePermitNode
  , Safety.examplePermitNode
  ]

lemma uniK9FamilyGovernanceGraph_decides_permit
    (claims : List ClaimQ) (claimant : ClaimantId) :
    graphDecide uniK9FamilyGovernanceGraph claims claimant =
      BinaryDecision.Permit := by
  simp [uniK9FamilyGovernanceGraph, Safety.examplePermitNode, graphDecide]

lemma uniK9FamilyGovernanceGraph_allLegitimacyAxioms :
    AllLegitimacyAxioms uniK9FamilyGovernanceGraph := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro claims k j hk hj hkj hdist hdeny
    have hfalse := hdeny
    simp [uniK9FamilyGovernanceGraph_decides_permit claims k] at hfalse
  · intro claims α hα j hj
    simp [uniK9FamilyGovernanceGraph_decides_permit]
  · intro claims k s' hs' j hk hdist hle hperm
    simp [uniK9FamilyGovernanceGraph_decides_permit]
  · intro claims k s_r hs_r hk hdist hperm
    simp [uniK9FamilyGovernanceGraph_decides_permit]

lemma uniK9FamilyGovernanceTrace_consistent :
    TraceConsistentWithGraph permitTrace uniK9FamilyGovernanceGraph := by
  intro t
  simp [TraceEventConsistentWithGraph, permitTrace]
  exact ⟨[permitClaim], by simp,
    uniK9FamilyGovernanceGraph_decides_permit [permitClaim] permitClaim.id⟩

def uniK9FamilyGovernedSystem : GovernedSystem 1 where
  graph := uniK9FamilyGovernanceGraph
  state := permitState
  trace := permitTrace
  -- Edgeless fixture: causal-safety layer is structurally trivial here.
  dag := noEdgeDAG 1
  governed := allGoverned 1
  trace_consistent := uniK9FamilyGovernanceTrace_consistent
  dag_reflects_graph := noEdge_reflects_graph 1 uniK9FamilyGovernanceGraph

def uniK9FamilySpectralGraph :
    GovGraph ℚ uniK9FamilyGovernedSystem.graph.weightedSize := by
  change GovGraph ℚ 9
  exact uniK9

def uniK9FamilySpectralSignal :
    Fin uniK9FamilyGovernedSystem.graph.weightedSize → ℚ := by
  change Fin 9 → ℚ
  exact sig9

noncomputable def uniK9FamilyKernelData :
    LegitimacyKernelData uniK9FamilyGovernedSystem where
  Witness := ReplayWitness
  certification := graphReplayCertification uniK9FamilyGovernedSystem.graph
  certification_consistent :=
    graphReplayCertification_consistent uniK9FamilyGovernedSystem.graph
  ObservedState := GovernanceState
  answer := stateGovernanceAnswer uniK9FamilyGovernedSystem
  observe := fun s : GovernanceState => s
  observeAnswer := stateGovernanceAnswer uniK9FamilyGovernedSystem
  answer_consistent := state_answer_consistent uniK9FamilyGovernedSystem
  actionSpace := idActionSpace
  algebra := fullSupervisoryAlgebra
  actionCapability := fun _ => 0
  spectralGraph := uniK9FamilySpectralGraph
  spectralSignal := uniK9FamilySpectralSignal
  toleranceParameter := 1 / 10
  signalRange := Legitimacy.signalRange uniK9FamilySpectralSignal
  signalRange_spec := rfl
  stratificationLayers := 0
  overrideEval := familyLayerEval
  overrideOvs := []

def uniK9FamilyGovernanceNonVacuousWitness :
    NonVacuousWitness uniK9FamilyGovernanceGraph permitTrace where
  wellFormed := by
    simp [uniK9FamilyGovernanceGraph, WellFormed]
  governedClaims := [permitClaim]
  governed_nonempty := by
    simp
  boundedDisposition := permitTrace_bounded
  permitEligibleClaims := [permitClaim]
  eligible_nonempty := by
    simp
  eligible_subset := by
    intro c hc
    simpa using hc
  permitEligible := permitTrace_permitEligible
  notRefusal := permitTrace_notRefusal
  notPermanentEscalation := permitTrace_notPermanentEscalation
  notDeadlock := permitTrace_notDeadlock

lemma uniK9FamilyGovernance_nonvacuous :
    NonVacuous uniK9FamilyGovernanceGraph permitTrace :=
  ⟨uniK9FamilyGovernanceNonVacuousWitness⟩

@[reducible]
noncomputable def uniK9FamilyRuntimeKernel :
    IsLegitimacyKernel uniK9FamilyKernelData where
  certifiable :=
    graphReplayCertification_certifiable uniK9FamilyGovernedSystem.graph
  observable := state_id_observable uniK9FamilyGovernedSystem
  corrigible :=
    kernelCorrigible_zero _ permit_corrigible (by intro a; rfl)
  compositionalSafety :=
    LegitimacyKernelData.kernelCausalSoundness_of_causalSoundness _
      (noEdge_causal_soundness 1 (allGoverned 1))
  nonVacuous :=
    LegitimacyKernelData.kernelNonVacuous_of_nonVacuous _
      uniK9FamilyGovernance_nonvacuous

/-- Concrete `uniK9` kernel data aligned with the nine-node structural native ASI family carrier. -/
theorem uniK9FamilyKernelData_familyAligned :
    FamilyAlignedKernelData uniK9FamilyKernelData uniK9 sig9 3 := by
  refine
    { carrier := uniK9_structuralCompleteSymmetric
      size_eq := ?_
      graph_eq := ?_
      signal_eq := ?_ }
  · rfl
  · rfl
  · rfl

theorem uniK9FamilyKernelData_spectralCarrierRepresentsGraph :
    SpectralCarrierRepresentsGraph uniK9FamilyGovernedSystem.graph
      uniK9FamilyKernelData.spectralGraph
      uniK9FamilyKernelData.spectralSignal where
  claimantProjects := by
    intro i
    refine ⟨⟨i.val, i.val + 1, by exact_mod_cast Nat.succ_pos i.val, []⟩, ?_, rfl⟩
    simp [GovernanceGraph.profileClaims]
  graphSize := by
    simp [uniK9FamilyGovernedSystem, uniK9FamilyGovernanceGraph,
      GovernanceGraph.weightedSize]
  canonicalProfileRecovery := by
    intro representative _hsize hclass i
    have hspectral :
        ∀ i : Fin uniK9FamilyGovernedSystem.graph.weightedSize,
          spectralCarrierDecision uniK9 sig9 i = BinaryDecision.Permit := by
      native_decide
    calc
      spectralCarrierDecision uniK9 sig9 i = BinaryDecision.Permit :=
        hspectral i
      _ = graphDecide uniK9FamilyGovernedSystem.graph
          uniK9FamilyGovernedSystem.graph.profileClaims i.val :=
        (uniK9FamilyGovernanceGraph_decides_permit
          uniK9FamilyGovernedSystem.graph.profileClaims i.val).symm
      _ = graphDecide representative representative.profileClaims i.val :=
        (hclass.2 i).symm
  peerSurfacePositiveCV := by
    intro pref tail _hsurface
    change 0 < uniK9.cv sig9
    rw [n9_cv_values.1]
    norm_num

/-- Unconditional semantic invariant for the concrete `uniK9` family-aligned kernel datum, discharged by the native carrier's own spectral certificate. -/
theorem uniK9_family_aligned_kernelInvariant :
    Safety.KernelInvariant uniK9FamilyKernelData :=
  { runtimeKernel := uniK9FamilyRuntimeKernel
    semanticBridge :=
      ⟨uniK9FamilyGovernanceGraph_allLegitimacyAxioms,
        uniK9FamilyKernelData_spectralCarrierRepresentsGraph,
        family_aligned_kernel_spectral
          uniK9FamilyKernelData uniK9 sig9 3
          uniK9FamilyKernelData_familyAligned⟩ }

/-- Carrier-specific native ASI bridge theorem for `uniK9`. The nine-node ASI signature premise is discharged from the concrete depth-3 RG witness. -/
theorem uniK9_family_aligned_native_asi_signature_kernelInvariant :
    Safety.KernelInvariant uniK9FamilyKernelData := by
  have hasi : ASISpectralSignatureN 9 80
      (GovGraph.rgTrajectory uniK9 sig9 80 3) :=
    uniK9_asiSpectralSignature_depth3 80 (by norm_num)
  let ctx : BridgeContext (n := 8) uniK9FamilyGovernedSystem :=
    { δ := 80
      target := GovGraph.rgTrajectory uniK9 sig9 80 3
      D := uniK9FamilyKernelData
      G := uniK9
      s := sig9
      depth := 3 }
  have htargetCtx :
      ctx.target = GovGraph.rgTrajectory ctx.G ctx.s ctx.δ ctx.depth := by
    change GovGraph.rgTrajectory uniK9 sig9 80 3 =
      GovGraph.rgTrajectory uniK9 sig9 80 3
    rfl
  exact
    native_asi_signature_kernelInvariant_of_family_aligned
      ctx
      uniK9FamilyKernelData_familyAligned
      hasi htargetCtx uniK9FamilyRuntimeKernel
      uniK9FamilyGovernanceGraph_allLegitimacyAxioms
      uniK9FamilyKernelData_spectralCarrierRepresentsGraph

/-- Concrete family-aligned toy bridge for the depth-3 `uniK5` ASI signature. -/
theorem uniK5_family_aligned_native_asi_signature_kernelInvariant :
    Safety.KernelInvariant Safety.exampleGovernanceKernelData := by
  let target : ℚ × ℚ := GovGraph.rgTrajectory uniK5 sig5 80 3
  have hasi : ASISpectralSignatureN 5 80 target := by
    exact ASISpectralSignatureN_five_of_ASISpectralSignature
      (by
        simpa [target] using
          (concrete_iterated_RG_n5_universality 80 (by norm_num)).1)
  let ctx : BridgeContext (n := 4) Safety.exampleGovernedSystem :=
    { δ := 80
      target := target
      D := Safety.exampleGovernanceKernelData
      G := uniK5
      s := sig5
      depth := 3 }
  have htargetCtx :
      ctx.target = GovGraph.rgTrajectory ctx.G ctx.s ctx.δ ctx.depth := by
    change target = GovGraph.rgTrajectory uniK5 sig5 80 3
    rfl
  exact
    native_asi_signature_kernelInvariant_of_family_aligned
      ctx
      exampleGovernanceKernelData_familyAligned_uniK5
      hasi htargetCtx Safety.exampleGovernanceRuntimeKernel
      Safety.exampleGovernanceGraph_allLegitimacyAxioms
      Safety.exampleGovernance_spectralCarrierRepresentsGraph

end ASIBridge

end Legitimacy
