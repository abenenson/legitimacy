/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Extract.Soundness
import Legitimacy.Safety.KernelSafety
import Legitimacy.Safety.KernelSafety.StatefulExamples

/-!
# Legitimacy.VerificationTrilemma

Ayushi Agarwal's 2026 verification-trilemma paper (arXiv:2603.08761, "On the
Formal Limits of Alignment Verification") frames a tradeoff between soundness,
polynomial-time tractability, and correctness on the full input domain.

This module states a framework-specific analogue, not a formal derivation
against Agarwal's exact complexity and full-domain predicates. The current
theorem proves soundness, audit-decision definedness, and failure of
definedness on all finite distributions for bounded-extractor legitimacy
audits. Agarwal-style polynomial-time tractability and full-domain correctness
are separate future verification-trilemma substrate work.
-/

set_option autoImplicit false

namespace Legitimacy

/-- A finite theorem-facing input distribution. The support is represented as a
list because the legitimacy audit only makes formal claims over finite extracted
source packages. -/
structure InputDistribution where
  /-- Finite support of bounded extractor inputs considered by the audit. -/
  support : List ExtractorInput
  deriving Repr

/-- Extracted governance graph plus the proof-carrying bounded extractor
contract that authorizes formal audit claims on a declared finite input set. -/
structure ExtractedGovernanceGraph where
  /-- Lean-side extracted graph subject audited by `governanceAdmissibilityVerdict`. -/
  subject : AuditSubject
  /-- Lean model of the extractor used at the kernel boundary. -/
  extract : KernelExtractor
  /-- Bounded extractor contract for this extracted graph family. -/
  contract : BoundedExtractorContract extract
  /-- Finite contracted input support covered by the audit claim. -/
  contractedInputs : List ExtractorInput
  /-- Every contracted input is inside the bounded extractor boundary. -/
  contractedInputs_wellFormed :
    ∀ src : ExtractorInput, src ∈ contractedInputs → src.WellFormed
  /-- The extracted graph satisfies the theorem-facing admissibility audit. -/
  admissibility : ExtractedGraphAdmissibilityContract subject

/-- The theorem-facing audit object is exactly an extracted governance graph
with its finite bounded-input contract. -/
abbrev LegitimacyAudit := ExtractedGovernanceGraph

/-- Build the legitimacy audit object from an extracted governance graph. -/
def legitimacyAudit (G : ExtractedGovernanceGraph) : LegitimacyAudit := G

/-- Audit-relevant inputs are finite distributions whose support stays inside
the bounded-extractor contract. This is the restricted-input clause: it is not
definitionally true for arbitrary distributions. -/
def AuditRelevantInputs
    (D : InputDistribution) (audit : LegitimacyAudit) : Prop :=
  ∀ src : ExtractorInput, src ∈ D.support → src ∈ audit.contractedInputs

/-- The audit is defined exactly on distributions whose finite support is
covered by the bounded extractor contract. -/
def IsAuditDefined (audit : LegitimacyAudit) (D : InputDistribution) : Prop :=
  AuditRelevantInputs D audit

/-- Executable theorem-facing decision surface. If any input lies outside the
finite contract, the audit is intentionally undefined. Otherwise, the decision
is the finite governance-admissibility verdict. -/
def auditDecision?
    (audit : LegitimacyAudit) (D : InputDistribution) : Option AuditVerdict :=
  if D.support.all (fun src => decide (src ∈ audit.contractedInputs)) then
    some (governanceAdmissibilityVerdict audit.subject)
  else
    none

/-- Soundness on the restricted input distribution: each supported source maps
to a semantic kernel under the bounded extractor contract, and the extracted
graph itself satisfies the admissibility audit. -/
def AuditSound (audit : LegitimacyAudit) (D : InputDistribution) : Prop :=
  (∀ src : ExtractorInput,
      src ∈ D.support → (audit.extract src).IsSemanticKernel) ∧
    ExtractedGraphAdmissibilityContract audit.subject

/-- Decision-definedness by finite execution: the audit has a concrete
framework verdict on the finite distribution. This is not Agarwal's
polynomial-time tractability predicate; the proof below only discharges the
list membership decision and `governanceAdmissibilityVerdict`. -/
def AuditDecisionDefined (audit : LegitimacyAudit) (D : InputDistribution) : Prop :=
  ∃ verdict : AuditVerdict, auditDecision? audit D = some verdict

/-- Definedness on all finite distributions. This is not Agarwal's correctness
on the full input domain; it records only whether the framework audit is
defined for every theorem-facing finite distribution. -/
def AuditDefinedOnAllDistributions (audit : LegitimacyAudit) : Prop :=
  ∀ D : InputDistribution, IsAuditDefined audit D

/-- Concrete unrestricted source package used as the negative witness:
over-bound, uncovered, and parser-dirty. -/
def unrestrictedMalformedExtractorInput : ExtractorInput where
  sourceId := "verification-trilemma/unrestricted-infinite-state"
  byteSize := 2
  sizeBound := 1
  coverageComplete := false
  parserErrors := 1

lemma unrestrictedMalformedExtractorInput_not_wellFormed :
    ¬ unrestrictedMalformedExtractorInput.WellFormed := by
  simp [ExtractorInput.WellFormed, unrestrictedMalformedExtractorInput]

/-- Singleton unrestricted distribution outside any contract whose members must
be well-formed bounded extractor inputs. -/
def unrestrictedMalformedDistribution : InputDistribution where
  support := [unrestrictedMalformedExtractorInput]

lemma unrestrictedMalformedInput_outside_contract
    (audit : LegitimacyAudit) :
    unrestrictedMalformedExtractorInput ∉ audit.contractedInputs := by
  intro hmem
  exact
    unrestrictedMalformedExtractorInput_not_wellFormed
      (audit.contractedInputs_wellFormed unrestrictedMalformedExtractorInput hmem)

private lemma support_all_contract_true
    (support contracted : List ExtractorInput)
    (hcovered :
      ∀ src : ExtractorInput, src ∈ support → src ∈ contracted) :
    support.all (fun src => decide (src ∈ contracted)) = true := by
  induction support with
  | nil =>
      simp
  | cons head tail ih =>
      have hhead : decide (head ∈ contracted) = true := by
        exact decide_eq_true (hcovered head (List.Mem.head tail))
      have htail :
          ∀ src : ExtractorInput, src ∈ tail → src ∈ contracted := by
        intro src hsrc
        exact hcovered src (List.Mem.tail head hsrc)
      simp [List.all, hhead, ih htail]

private lemma auditDecision_defined_relevant
    (audit : LegitimacyAudit) (D : InputDistribution)
    (hdefined : AuditDecisionDefined audit D) :
    AuditRelevantInputs D audit := by
  rcases hdefined with ⟨verdict, hsome⟩
  have hall :
      D.support.all (fun src => decide (src ∈ audit.contractedInputs)) = true := by
    cases hbool :
        D.support.all (fun src => decide (src ∈ audit.contractedInputs)) <;>
      simp [auditDecision?, hbool] at hsome ⊢
  intro src hsrc
  exact of_decide_eq_true ((List.all_eq_true.mp hall) src hsrc)

/-- Within the current theorem-facing `LegitimacyAudit` type, decision-definedness
is stronger than the semantic part of soundness: if the decision surface returns
a verdict, the finite support is inside the well-formed contract, so bounded
extractor soundness and the packaged admissibility witness discharge
`AuditSound`. This records why the soundness clause has no independent
counter-witness in this substrate. -/
theorem audit_decision_defined_implies_soundness
    (audit : LegitimacyAudit) (D : InputDistribution)
    (hdefined : AuditDecisionDefined audit D) :
    AuditSound audit D := by
  constructor
  · intro src hsrc
    exact
      bounded_extractor_contract_sound audit.extract audit.contract src
        (audit.contractedInputs_wellFormed src
          (auditDecision_defined_relevant audit D hdefined src hsrc))
  · exact audit.admissibility

/-- No theorem-facing `LegitimacyAudit` is defined on all finite distributions:
the unrestricted malformed input is outside every finite contract whose members
must be well formed. This records why the all-distributions clause has no
independent counter-witness in this substrate. -/
theorem audit_defined_on_all_distributions_impossible
    (audit : LegitimacyAudit) :
    ¬ AuditDefinedOnAllDistributions audit := by
  intro hgeneral
  have hmem :
      unrestrictedMalformedExtractorInput ∈ audit.contractedInputs :=
    hgeneral unrestrictedMalformedDistribution unrestrictedMalformedExtractorInput (by
      simp [unrestrictedMalformedDistribution])
  exact
    unrestrictedMalformedExtractorInput_not_wellFormed
      (audit.contractedInputs_wellFormed unrestrictedMalformedExtractorInput hmem)

/-- Verification-trilemma positioning lemma. Against the 2026
verification-trilemma result (arXiv:2603.08761), the legitimacy audit occupies
the `AuditSound` x `AuditDecisionDefined` corner only on structurally restricted
finite bounded-extractor inputs, and constructively refuses
`AuditDefinedOnAllDistributions`. This is the current substrate's analogue of
the trilemma, not a polynomial-time/full-domain theorem. -/
theorem legitimacy_audit_diagonal_positioning
    (G : ExtractedGovernanceGraph) (D : InputDistribution)
    (hRelevant : AuditRelevantInputs D (legitimacyAudit G)) :
    AuditSound (legitimacyAudit G) D ∧
      AuditDecisionDefined (legitimacyAudit G) D ∧
        ¬ AuditDefinedOnAllDistributions (legitimacyAudit G) := by
  constructor
  · constructor
    · intro src hsrc
      exact
        bounded_extractor_contract_sound G.extract G.contract src
          (G.contractedInputs_wellFormed src (hRelevant src hsrc))
    · exact G.admissibility
  · constructor
    · refine ⟨governanceAdmissibilityVerdict G.subject, ?_⟩
      have hall :
          D.support.all (fun src => decide (src ∈ G.contractedInputs)) = true :=
        support_all_contract_true D.support G.contractedInputs hRelevant
      change
        (if D.support.all (fun src => decide (src ∈ G.contractedInputs)) then
          some (governanceAdmissibilityVerdict G.subject)
        else
          none) = some (governanceAdmissibilityVerdict G.subject)
      rw [hall]
      simp
    · exact audit_defined_on_all_distributions_impossible (legitimacyAudit G)

/-! ## Tightness witnesses -/

/-- Concrete compiler-audit graph packaged as a verification-trilemma
positioning extracted graph. The graph verdict uses the existing
self-legitimacy theorem, while the kernel side uses the existing bounded
example extractor contract. -/
noncomputable def compilerAuditTrilemmaExtractedGraph : ExtractedGovernanceGraph where
  subject := compilerAuditGraph
  extract := Safety.exampleGovernanceKernelExtractor
  contract := Safety.exampleGovernanceKernelExtractor_contract
  contractedInputs := [compilerAuditExtractorInput]
  contractedInputs_wellFormed := by
    intro src hsrc
    simp at hsrc
    subst src
    simp [ExtractorInput.WellFormed, compilerAuditExtractorInput]
  admissibility := compiler_audit_satisfies_extracted_graph_admissibility_contract

/-- Finite audit-relevant distribution for the compiler-audit tightness
witness. -/
def compilerAuditTrilemmaDistribution : InputDistribution where
  support := [compilerAuditExtractorInput]

lemma compilerAuditTrilemmaDistribution_relevant :
    AuditRelevantInputs compilerAuditTrilemmaDistribution
      (legitimacyAudit compilerAuditTrilemmaExtractedGraph) := by
  intro src hsrc
  simp [compilerAuditTrilemmaDistribution] at hsrc
  subst src
  exact List.Mem.head _

/-- Soundness witness: the concrete compiler-audit distribution is inside the
bounded extractor contract and therefore receives the semantic-kernel and
admissibility conclusions. -/
theorem compiler_audit_trilemma_soundness_witness :
    AuditSound (legitimacyAudit compilerAuditTrilemmaExtractedGraph)
      compilerAuditTrilemmaDistribution :=
  (legitimacy_audit_diagonal_positioning compilerAuditTrilemmaExtractedGraph
    compilerAuditTrilemmaDistribution compilerAuditTrilemmaDistribution_relevant).1

/-- Generality-failure witness: the unrestricted malformed source package is
outside the compiler-audit bounded extractor contract, so the audit is
undefined on that distribution. -/
theorem trilemma_definedness_failure_witness :
    ¬ IsAuditDefined (legitimacyAudit compilerAuditTrilemmaExtractedGraph)
      unrestrictedMalformedDistribution := by
  intro hdefined
  have hmem :
      unrestrictedMalformedExtractorInput ∈
        (legitimacyAudit compilerAuditTrilemmaExtractedGraph).contractedInputs :=
    hdefined unrestrictedMalformedExtractorInput (by
      simp [unrestrictedMalformedDistribution])
  exact
    unrestrictedMalformedExtractorInput_not_wellFormed
      ((legitimacyAudit compilerAuditTrilemmaExtractedGraph).contractedInputs_wellFormed
        unrestrictedMalformedExtractorInput hmem)

/-- The compiler-audit extractor is a constant Lean model that still emits the
semantic example artifact on the malformed distribution. Thus this distribution
can witness failure of decision-definedness without also breaking soundness. -/
theorem compiler_audit_malformed_distribution_sound :
    AuditSound (legitimacyAudit compilerAuditTrilemmaExtractedGraph)
      unrestrictedMalformedDistribution := by
  constructor
  · intro src hsrc
    simp [unrestrictedMalformedDistribution] at hsrc
    subst src
    change
      (Safety.exampleGovernanceKernelExtractor
        unrestrictedMalformedExtractorInput).IsSemanticKernel
    simp [Safety.exampleGovernanceKernelExtractor,
      Safety.exampleGovernanceExtractedKernelArtifact,
      ExtractedKernelArtifact.IsSemanticKernel]
    exact Safety.exampleGovernanceSemanticKernel
  · exact compilerAuditTrilemmaExtractedGraph.admissibility

/-- Headline concrete corollary for the compiler-audit witness. -/
theorem compiler_audit_diagonal_positioning :
    AuditSound (legitimacyAudit compilerAuditTrilemmaExtractedGraph)
        compilerAuditTrilemmaDistribution ∧
      AuditDecisionDefined (legitimacyAudit compilerAuditTrilemmaExtractedGraph)
        compilerAuditTrilemmaDistribution ∧
        ¬ AuditDefinedOnAllDistributions
          (legitimacyAudit compilerAuditTrilemmaExtractedGraph) :=
  legitimacy_audit_diagonal_positioning compilerAuditTrilemmaExtractedGraph
    compilerAuditTrilemmaDistribution compilerAuditTrilemmaDistribution_relevant

/-! ## Drop-test witnesses

These are proof-bearing smoke tests for the theorem shape. They do not encode
failing Lean commands; instead they pin the positive and negative surfaces a
reviewer would check manually when mutating the headline theorem.
-/

/-- Drop-test: if the soundness conjunct is removed, the decision-definedness
and all-distribution refusal clauses still discharge from the same proof. -/
theorem compiler_audit_trilemma_without_soundness_clause :
    AuditDecisionDefined (legitimacyAudit compilerAuditTrilemmaExtractedGraph)
        compilerAuditTrilemmaDistribution ∧
      ¬ AuditDefinedOnAllDistributions
        (legitimacyAudit compilerAuditTrilemmaExtractedGraph) :=
  compiler_audit_diagonal_positioning.2

/-- Drop-test: if the decision-definedness conjunct is removed, the soundness
and all-distribution refusal clauses still discharge from the same proof. -/
theorem compiler_audit_trilemma_without_decision_defined_clause :
    AuditSound (legitimacyAudit compilerAuditTrilemmaExtractedGraph)
        compilerAuditTrilemmaDistribution ∧
      ¬ AuditDefinedOnAllDistributions
        (legitimacyAudit compilerAuditTrilemmaExtractedGraph) :=
  ⟨compiler_audit_diagonal_positioning.1,
    compiler_audit_diagonal_positioning.2.2⟩

/-- Drop-test: if the all-distribution refusal conjunct is removed, the
soundness and decision-definedness clauses still discharge from the same proof. -/
theorem compiler_audit_trilemma_without_all_distributions_clause :
    AuditSound (legitimacyAudit compilerAuditTrilemmaExtractedGraph)
        compilerAuditTrilemmaDistribution ∧
      AuditDecisionDefined (legitimacyAudit compilerAuditTrilemmaExtractedGraph)
        compilerAuditTrilemmaDistribution :=
  ⟨compiler_audit_diagonal_positioning.1,
    compiler_audit_diagonal_positioning.2.1⟩

/-- Drop-test for the relevance hypothesis: the unrestricted malformed
distribution is not audit-relevant for any extracted graph whose contracted
inputs are all well formed. -/
theorem unrestricted_distribution_not_relevant
    (G : ExtractedGovernanceGraph) :
    ¬ AuditRelevantInputs unrestrictedMalformedDistribution (legitimacyAudit G) := by
  intro hRelevant
  have hmem :
      unrestrictedMalformedExtractorInput ∈
        (legitimacyAudit G).contractedInputs :=
    hRelevant unrestrictedMalformedExtractorInput (by
      simp [unrestrictedMalformedDistribution])
  exact
    unrestrictedMalformedExtractorInput_not_wellFormed
      ((legitimacyAudit G).contractedInputs_wellFormed
        unrestrictedMalformedExtractorInput hmem)

/-- Trivial audit replacement used by the drop test below: it ignores the
bounded extractor contract and always returns a fixed verdict. -/
def auditConstant? (_D : InputDistribution) : Option AuditVerdict :=
  some AuditVerdict.legitimate

/-- Drop-test for replacing the legitimacy audit with a constant verdict:
the constant audit decides the unrestricted malformed distribution, while the
bounded legitimacy audit is intentionally undefined there. -/
theorem audit_constant_does_not_track_bounded_definedness :
    auditConstant? unrestrictedMalformedDistribution = some AuditVerdict.legitimate ∧
      auditDecision? (legitimacyAudit compilerAuditTrilemmaExtractedGraph)
          unrestrictedMalformedDistribution = none := by
  constructor
  · rfl
  · have hnot :
        unrestrictedMalformedExtractorInput ∉
          (legitimacyAudit compilerAuditTrilemmaExtractedGraph).contractedInputs := by
      exact
        unrestrictedMalformedInput_outside_contract
          (audit := legitimacyAudit compilerAuditTrilemmaExtractedGraph)
    simp [auditDecision?, unrestrictedMalformedDistribution, hnot]

/-- Concrete false evaluation for the decision-definedness clause on the
malformed distribution: the bounded audit returns `none`, not a verdict. -/
theorem compiler_audit_malformed_distribution_decision_none :
    auditDecision? (legitimacyAudit compilerAuditTrilemmaExtractedGraph)
        unrestrictedMalformedDistribution = none :=
  audit_constant_does_not_track_bounded_definedness.2

/-- The malformed distribution is not decision-defined for the compiler audit.
The proof consumes the concrete `none` evaluation above. -/
theorem compiler_audit_malformed_distribution_not_decision_defined :
    ¬ AuditDecisionDefined (legitimacyAudit compilerAuditTrilemmaExtractedGraph)
      unrestrictedMalformedDistribution := by
  intro hdefined
  rcases hdefined with ⟨verdict, hsome⟩
  rw [compiler_audit_malformed_distribution_decision_none] at hsome
  cases hsome

/-- Genuine independence witness for the decision-definedness clause: the
compiler audit remains sound and non-general on the malformed finite
distribution, while the decision-definedness clause itself fails. -/
theorem trilemma_decision_defined_independent :
    AuditSound (legitimacyAudit compilerAuditTrilemmaExtractedGraph)
        unrestrictedMalformedDistribution ∧
      ¬ AuditDefinedOnAllDistributions
        (legitimacyAudit compilerAuditTrilemmaExtractedGraph) ∧
        ¬ AuditDecisionDefined
          (legitimacyAudit compilerAuditTrilemmaExtractedGraph)
          unrestrictedMalformedDistribution :=
  ⟨compiler_audit_malformed_distribution_sound,
    audit_defined_on_all_distributions_impossible
      (legitimacyAudit compilerAuditTrilemmaExtractedGraph),
    compiler_audit_malformed_distribution_not_decision_defined⟩

end Legitimacy
