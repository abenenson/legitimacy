/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.MultiAgentComposition.Core

/-!
# Legitimacy.MultiAgentComposition.Certificates

Failure certificates and kernel-aware extraction for incompatible cross-agent
composition surfaces.
-/

set_option autoImplicit false

namespace Legitimacy

inductive CrossAgentCompatibilityFailureKind where
  | authorityLattice
  | noninterference
  | monotoneEscalation
  | sacrificeIndex
  | bridgePreservation
  deriving Repr, DecidableEq

/-- A minimal cross-agent sacrifice certificate records exactly one failed
compatibility boundary. The failed predicate is retained as evidence rather
than compressed into a generic boolean failure. -/
structure CrossAgentSacrificeCertificate
    (sys : MultiAgentSystem) where
  failedCondition : CrossAgentCompatibilityFailureKind
  failed :
    match failedCondition with
    | CrossAgentCompatibilityFailureKind.authorityLattice =>
        ¬ AuthorityLatticeCompatible sys
    | CrossAgentCompatibilityFailureKind.noninterference =>
        ¬ NoninterferenceOrDeclared sys
    | CrossAgentCompatibilityFailureKind.monotoneEscalation =>
        ¬ MonotoneEscalationComposition sys
    | CrossAgentCompatibilityFailureKind.sacrificeIndex =>
        ¬ CompatibleSacrificeIndices sys
    | CrossAgentCompatibilityFailureKind.bridgePreservation =>
        ¬ CrossAgentBridgePreservation sys

/-- Projection of a certificate's failure-kind into the concrete failed
compatibility predicate. This is the content the negative theorem promises,
not a reflexive property of the certificate value. -/
def CrossAgentCertificateFailureClause
    {sys : MultiAgentSystem}
    (cert : CrossAgentSacrificeCertificate sys) : Prop :=
  match cert.failedCondition with
  | CrossAgentCompatibilityFailureKind.authorityLattice =>
      ¬ AuthorityLatticeCompatible sys
  | CrossAgentCompatibilityFailureKind.noninterference =>
      ¬ NoninterferenceOrDeclared sys
  | CrossAgentCompatibilityFailureKind.monotoneEscalation =>
      ¬ MonotoneEscalationComposition sys
  | CrossAgentCompatibilityFailureKind.sacrificeIndex =>
      ¬ CompatibleSacrificeIndices sys
  | CrossAgentCompatibilityFailureKind.bridgePreservation =>
      ¬ CrossAgentBridgePreservation sys

/-- Validity for the emitted cross-agent certificate: its stored failed
condition projects to a real failed compatibility predicate. -/
def IsValidCrossAgentCertificate
    {sys : MultiAgentSystem}
    (cert : CrossAgentSacrificeCertificate sys) : Prop :=
  CrossAgentCertificateFailureClause cert

/-- Edge-local projection of a certificate failure kind. This records the
missing witness at the certified boundary rather than merely restating the
system-level failed compatibility predicate. -/
def CrossAgentFailureAtKind
    (sys : MultiAgentSystem)
    (kind : CrossAgentCompatibilityFailureKind)
    (edge : CrossAgentEdge) : Prop :=
  match kind with
  | CrossAgentCompatibilityFailureKind.authorityLattice =>
      ¬ Nonempty (CrossAgentAuthorityLatticeWitness sys edge)
  | CrossAgentCompatibilityFailureKind.noninterference =>
      ¬ Nonempty (CrossAgentNoninterferenceWitness sys edge)
  | CrossAgentCompatibilityFailureKind.monotoneEscalation =>
      ¬ Nonempty (CrossAgentEscalationMonotonicityWitness sys edge)
  | CrossAgentCompatibilityFailureKind.sacrificeIndex =>
      ¬ Nonempty (CrossAgentSacrificeIndexWitness sys edge)
  | CrossAgentCompatibilityFailureKind.bridgePreservation =>
      ¬ Nonempty (CrossAgentBridgeWitness sys edge)

/-- Kernel-derived endpoint soundness for a concrete cross-agent edge. The
endpoint witness is quantified so the property remains meaningful even when
the failed edge is also missing a richer compatibility witness. -/
def KernelDerivedEndpointSoundness
    (sys : MultiAgentSystem) (edge : CrossAgentEdge) : Prop :=
  ∀ endpoints : CrossAgentEndpointWitness sys edge,
    CausalSoundness endpoints.source.sys.dag endpoints.source.sys.governed ∧
      CausalSoundness endpoints.target.sys.dag endpoints.target.sys.governed

/-- Kernel-aware, edge-local failure content: a concrete boundary lacks the
compatibility witness named by the certificate while every declared endpoint
for that boundary retains the causal-soundness projection derived from its
semantic kernel. -/
def KernelAwareCrossAgentFailureAt
    (sys : MultiAgentSystem)
    (kind : CrossAgentCompatibilityFailureKind)
    (edge : CrossAgentEdge) : Prop :=
  CrossAgentFailureAtKind sys kind edge ∧
    KernelDerivedEndpointSoundness sys edge

/-- Kernel-aware validity for an emitted cross-agent certificate. The
certificate still projects to a real failed compatibility predicate. If the
composition surface is nonempty, the certificate also identifies a concrete
edge whose failed witness matches the certificate kind and whose declared
endpoints carry semantic-kernel-derived causal soundness. Empty composition is
recorded explicitly because there is then no cross-agent boundary to name. -/
def KernelAwareCrossAgentCertificate
    {sys : MultiAgentSystem}
    (cert : CrossAgentSacrificeCertificate sys) : Prop :=
  CrossAgentCertificateFailureClause cert ∧
    (sys.composition_edges = [] ∨
      ∃ edge, edge ∈ sys.composition_edges ∧
        KernelAwareCrossAgentFailureAt sys cert.failedCondition edge)

private theorem authority_failure_at_of_not_compatible
    {sys : MultiAgentSystem}
    (hnonempty : sys.composition_edges ≠ [])
    (hnot : ¬ AuthorityLatticeCompatible sys) :
    ∃ edge, edge ∈ sys.composition_edges ∧
      ¬ Nonempty (CrossAgentAuthorityLatticeWitness sys edge) := by
  by_contra hnone
  have hwitnessed :
      ∀ edge, edge ∈ sys.composition_edges →
        Nonempty (CrossAgentAuthorityLatticeWitness sys edge) := by
    intro edge hedge
    by_contra hmissing
    exact hnone ⟨edge, hedge, hmissing⟩
  exact hnot
    { nonempty_composition := hnonempty
      witnessed_edges := hwitnessed }

private theorem noninterference_failure_at_of_not_compatible
    {sys : MultiAgentSystem}
    (hnonempty : sys.composition_edges ≠ [])
    (hnot : ¬ NoninterferenceOrDeclared sys) :
    ∃ edge, edge ∈ sys.composition_edges ∧
      ¬ Nonempty (CrossAgentNoninterferenceWitness sys edge) := by
  by_contra hnone
  have hwitnessed :
      ∀ edge, edge ∈ sys.composition_edges →
        Nonempty (CrossAgentNoninterferenceWitness sys edge) := by
    intro edge hedge
    by_contra hmissing
    exact hnone ⟨edge, hedge, hmissing⟩
  exact hnot
    { nonempty_composition := hnonempty
      witnessed_edges := hwitnessed }

private theorem monotone_failure_at_of_not_compatible
    {sys : MultiAgentSystem}
    (hnonempty : sys.composition_edges ≠ [])
    (hnot : ¬ MonotoneEscalationComposition sys) :
    ∃ edge, edge ∈ sys.composition_edges ∧
      ¬ Nonempty (CrossAgentEscalationMonotonicityWitness sys edge) := by
  by_contra hnone
  have hwitnessed :
      ∀ edge, edge ∈ sys.composition_edges →
        Nonempty (CrossAgentEscalationMonotonicityWitness sys edge) := by
    intro edge hedge
    by_contra hmissing
    exact hnone ⟨edge, hedge, hmissing⟩
  exact hnot
    { nonempty_composition := hnonempty
      witnessed_edges := hwitnessed }

private theorem sacrifice_failure_at_of_not_compatible
    {sys : MultiAgentSystem}
    (hnonempty : sys.composition_edges ≠ [])
    (hnot : ¬ CompatibleSacrificeIndices sys) :
    ∃ edge, edge ∈ sys.composition_edges ∧
      ¬ Nonempty (CrossAgentSacrificeIndexWitness sys edge) := by
  by_contra hnone
  have hwitnessed :
      ∀ edge, edge ∈ sys.composition_edges →
        Nonempty (CrossAgentSacrificeIndexWitness sys edge) := by
    intro edge hedge
    by_contra hmissing
    exact hnone ⟨edge, hedge, hmissing⟩
  exact hnot
    { nonempty_composition := hnonempty
      witnessed_edges := hwitnessed }

private theorem bridge_failure_at_of_not_compatible
    {sys : MultiAgentSystem}
    (hnonempty : sys.composition_edges ≠ [])
    (hnot : ¬ CrossAgentBridgePreservation sys) :
    ∃ edge, edge ∈ sys.composition_edges ∧
      ¬ Nonempty (CrossAgentBridgeWitness sys edge) := by
  by_contra hnone
  have hwitnessed :
      ∀ edge, edge ∈ sys.composition_edges →
        Nonempty (CrossAgentBridgeWitness sys edge) := by
    intro edge hedge
    by_contra hmissing
    exact hnone ⟨edge, hedge, hmissing⟩
  exact hnot
    { nonempty_composition := hnonempty
      witnessed_edges := hwitnessed }

lemma CrossAgentSacrificeCertificate.failure_clause
    {sys : MultiAgentSystem}
    (cert : CrossAgentSacrificeCertificate sys) :
    CrossAgentCertificateFailureClause cert := by
  cases cert with
  | mk failedCondition failed =>
      cases failedCondition <;> exact failed

/-- If any compatibility condition fails, the composed system either emits a
minimal cross-agent sacrifice certificate whose failure-kind projects to the
actual failed compatibility predicate. This is the formal negative half of
"kernel-governed agents do not automatically compose." The former
single-field Alabama wrapper is intentionally absent: monotone-escalation
failure is carried by the same certificate vocabulary as the other four
compatibility failures. -/
lemma multi_agent_failure_emits_valid_certificate
    (sys : MultiAgentSystem)
    (hsemantic_agents :
      ∀ agent ∈ sys.agents, IsSemanticLegitimacyKernel agent.kernel)
    (hfail : ¬ AllMultiAgentCompatibilityConditions sys) :
    (∃ cert : CrossAgentSacrificeCertificate sys,
        IsValidCrossAgentCertificate cert ∧
          CrossAgentCertificateFailureClause cert ∧
          KernelAwareCrossAgentCertificate cert) := by
  classical
  have hendpointSound :
      ∀ edge, KernelDerivedEndpointSoundness sys edge := by
    intro edge endpoints
    exact
      ⟨causalSoundness_of_semantic_kernel
          (hsemantic_agents endpoints.source endpoints.source_mem),
        causalSoundness_of_semantic_kernel
          (hsemantic_agents endpoints.target endpoints.target_mem)⟩
  by_cases hauthority : AuthorityLatticeCompatible sys
  · by_cases hnoninterference : NoninterferenceOrDeclared sys
    · by_cases hmonotone : MonotoneEscalationComposition sys
      · by_cases hsacrifice : CompatibleSacrificeIndices sys
        · by_cases hbridge : CrossAgentBridgePreservation sys
          · exact False.elim
              (hfail
                ⟨hauthority, hnoninterference, hmonotone,
                  hsacrifice, hbridge⟩)
          · let cert : CrossAgentSacrificeCertificate sys :=
              { failedCondition :=
                  CrossAgentCompatibilityFailureKind.bridgePreservation
                failed := hbridge }
            exact
              ⟨cert, cert.failure_clause, cert.failure_clause,
                by
                  refine ⟨cert.failure_clause, ?_⟩
                  by_cases hempty : sys.composition_edges = []
                  · exact Or.inl hempty
                  · right
                    obtain ⟨edge, hedge, hmissing⟩ :=
                      bridge_failure_at_of_not_compatible hempty hbridge
                    exact ⟨edge, hedge, hmissing, hendpointSound edge⟩⟩
        · let cert : CrossAgentSacrificeCertificate sys :=
            { failedCondition :=
                CrossAgentCompatibilityFailureKind.sacrificeIndex
              failed := hsacrifice }
          exact
            ⟨cert, cert.failure_clause, cert.failure_clause,
              by
                refine ⟨cert.failure_clause, ?_⟩
                by_cases hempty : sys.composition_edges = []
                · exact Or.inl hempty
                · right
                  obtain ⟨edge, hedge, hmissing⟩ :=
                    sacrifice_failure_at_of_not_compatible hempty hsacrifice
                  exact ⟨edge, hedge, hmissing, hendpointSound edge⟩⟩
      · let cert : CrossAgentSacrificeCertificate sys :=
          { failedCondition :=
              CrossAgentCompatibilityFailureKind.monotoneEscalation
            failed := hmonotone }
        exact
          ⟨cert, cert.failure_clause, cert.failure_clause,
            by
              refine ⟨cert.failure_clause, ?_⟩
              by_cases hempty : sys.composition_edges = []
              · exact Or.inl hempty
              · right
                obtain ⟨edge, hedge, hmissing⟩ :=
                  monotone_failure_at_of_not_compatible hempty hmonotone
                exact ⟨edge, hedge, hmissing, hendpointSound edge⟩⟩
    · let cert : CrossAgentSacrificeCertificate sys :=
        { failedCondition :=
            CrossAgentCompatibilityFailureKind.noninterference
          failed := hnoninterference }
      exact
        ⟨cert, cert.failure_clause, cert.failure_clause,
          by
            refine ⟨cert.failure_clause, ?_⟩
            by_cases hempty : sys.composition_edges = []
            · exact Or.inl hempty
            · right
              obtain ⟨edge, hedge, hmissing⟩ :=
                noninterference_failure_at_of_not_compatible hempty
                  hnoninterference
              exact ⟨edge, hedge, hmissing, hendpointSound edge⟩⟩
  · let cert : CrossAgentSacrificeCertificate sys :=
      { failedCondition :=
          CrossAgentCompatibilityFailureKind.authorityLattice
        failed := hauthority }
    exact
      ⟨cert, cert.failure_clause, cert.failure_clause,
        by
          refine ⟨cert.failure_clause, ?_⟩
          by_cases hempty : sys.composition_edges = []
          · exact Or.inl hempty
          · right
            obtain ⟨edge, hedge, hmissing⟩ :=
              authority_failure_at_of_not_compatible hempty hauthority
            exact ⟨edge, hedge, hmissing, hendpointSound edge⟩⟩

end Legitimacy
