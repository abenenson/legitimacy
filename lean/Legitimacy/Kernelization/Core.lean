/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.SafetySpecReduction
import Legitimacy.Results.SemanticBridge

/-!
# Legitimacy.Kernelization.Core

Authority-surface vocabulary, hidden-authority certificates, and the kernelization-honesty extractor contract.
-/

set_option autoImplicit false

namespace Legitimacy

namespace Safety

/-! ## Authority-surface vocabulary -/

abbrev AuthorityNodeId := String

/-- Directed authority edge in the reported or effective authority surface. -/
structure AuthorityEdge where
  fromNode : AuthorityNodeId
  toNode : AuthorityNodeId
  deriving Repr, DecidableEq

/-- Structural authority graph used by the kernelization extractor. The
`edges` list records ordinary authority flow; `overrides` records ancestor
override authority separately so hidden overrides do not get collapsed into
ordinary reachability. -/
structure AuthorityGraph where
  nodes : List AuthorityNodeId
  edges : List AuthorityEdge
  overrides : List AuthorityEdge
  deriving Repr, DecidableEq

def HasAuthorityEdge (graph : AuthorityGraph) (edge : AuthorityEdge) : Prop :=
  edge ∈ graph.edges

def HasAuthorityOverride (graph : AuthorityGraph) (edge : AuthorityEdge) : Prop :=
  edge ∈ graph.overrides

def HasAuthoritySurface (graph : AuthorityGraph) (edge : AuthorityEdge) : Prop :=
  HasAuthorityEdge graph edge ∨ HasAuthorityOverride graph edge

/-- Computed ordinary-edge difference: edges effective governance can use that
are absent from the reported authority surface. -/
def AuthorityEdgeDifference
    (effective reported : AuthorityGraph) : List AuthorityEdge :=
  effective.edges.filter fun edge => !reported.edges.contains edge

/-- Computed override difference: override edges effective governance can use
that are absent from the reported authority surface. -/
def AuthorityOverrideDifference
    (effective reported : AuthorityGraph) : List AuthorityEdge :=
  effective.overrides.filter fun edge => !reported.overrides.contains edge

/-- Adjacent edge list induced by a concrete authority route. -/
def pathAuthorityEdges : List AuthorityNodeId → List AuthorityEdge
  | fromNode :: toNode :: rest =>
      { fromNode := fromNode, toNode := toNode } ::
        pathAuthorityEdges (toNode :: rest)
  | _ => []

/-- Every adjacent decision in the route is permitted by the graph. -/
def AuthorityPathPermitted (graph : AuthorityGraph)
    (path : List AuthorityNodeId) : Prop :=
  ∀ edge : AuthorityEdge, edge ∈ pathAuthorityEdges path →
    HasAuthorityEdge graph edge

/-- Route target, when the route is nonempty. -/
def routeTarget? : List AuthorityNodeId → Option AuthorityNodeId
  | [] => none
  | [node] => some node
  | _ :: rest => routeTarget? rest

/-- Direct edge between the first and last node of a route with at least two
nodes. -/
def routeDirectEdge? : List AuthorityNodeId → Option AuthorityEdge
  | source :: second :: rest =>
      match routeTarget? (second :: rest) with
      | some target => some { fromNode := source, toNode := target }
      | none => none
  | _ => none

/-- A route is edge-permitted when it has a real endpoint pair and every adjacent
edge is present in the graph. -/
def IsEdgePermittedRoute (graph : AuthorityGraph)
    (route : List AuthorityNodeId) : Prop :=
  2 ≤ route.length ∧ AuthorityPathPermitted graph route

/-- A permitted route is a bypass when its endpoint-to-endpoint direct authority
edge is not present in the graph. -/
def IsEdgePermittedBypass (graph : AuthorityGraph)
    (route : List AuthorityNodeId) : Prop :=
  IsEdgePermittedRoute graph route ∧
    match routeDirectEdge? route with
    | some edge => ¬ HasAuthorityEdge graph edge
    | none => False

/-- Computed subroutes obtained by deleting zero or more nodes while preserving
order. This keeps bypass minimality finite and executable. -/
def routeSublists : List AuthorityNodeId → List (List AuthorityNodeId)
  | [] => [[]]
  | node :: rest =>
      let tail := routeSublists rest
      tail ++ tail.map (fun shorter => node :: shorter)

/-- Finite proper-subroute relation used by bypass minimality. It is computed
from concrete route deletions, so examples discharge by enumerating actual
subroutes rather than by restating witness fields. -/
def ProperRouteSublist
    (shorter route : List AuthorityNodeId) : Prop :=
  shorter ∈ routeSublists route ∧ shorter ≠ route

/-- Reported and effective authority surfaces are extensionally equivalent
when they expose the same ordinary edges and the same override edges. -/
def AuthorityExtensionallyEquivalent
    (reported effective : AuthorityGraph) : Prop :=
  (∀ edge : AuthorityEdge,
      HasAuthorityEdge reported edge ↔ HasAuthorityEdge effective edge) ∧
    (∀ edge : AuthorityEdge,
      HasAuthorityOverride reported edge ↔
        HasAuthorityOverride effective edge)

noncomputable instance instDecidableAuthorityExtensionallyEquivalent
    (reported effective : AuthorityGraph) :
    Decidable (AuthorityExtensionallyEquivalent reported effective) := by
  classical
  infer_instance

/-- Bounded source evidence for a structural authority edge. -/
def SourceDerivesEdge (sourceEdges : List AuthorityEdge)
    (edge : AuthorityEdge) : Prop :=
  edge ∈ sourceEdges

/-- Permitted source-evidence derivations for authority edges. The present
contract intentionally allows only bounded source edges; later extensions can
add named constructors for audited derivation rules without changing the gap
predicate's shape. -/
inductive SourceEdgeDerivation
    (sourceEdges : List AuthorityEdge) (edge : AuthorityEdge) : Prop where
  | source :
      edge ∈ sourceEdges → SourceEdgeDerivation sourceEdges edge

def SourceEvidenceDerivable
    (sourceEdges : List AuthorityEdge) (edge : AuthorityEdge) : Prop :=
  ∃ _derivation : SourceEdgeDerivation sourceEdges edge, True

lemma sourceEvidenceDerivable_iff
    (sourceEdges : List AuthorityEdge) (edge : AuthorityEdge) :
    SourceEvidenceDerivable sourceEdges edge ↔
      SourceDerivesEdge sourceEdges edge := by
  constructor
  · rintro ⟨derivation, _⟩
    cases derivation with
    | source hsource => exact hsource
  · intro hsource
    exact ⟨SourceEdgeDerivation.source hsource, trivial⟩

/-! ## Kernelization observations and certificates -/

/-- Ordered semantic-kernel obligations that a semantic-bridge certificate can
pinpoint. The order is structural: runtime kernel obligations are checked before
the semantic bridge contract layered on top of them. -/
inductive SemanticFailureLocus where
  | runtimeKernel : SemanticFailureLocus
  | semanticBridge : SemanticFailureLocus
  deriving Repr, DecidableEq

/-- Branch-level extractor output recorded by a governance observation.

The witness-bearing certificate and clean-witness payloads remain indexed by
the observation and are defined below. This core branch vocabulary is therefore
the non-recursive part every observation can carry natively, while extractor
contracts still supply the payload soundness proofs. -/
inductive KernelizationExtractorBranch where
  | clean
  | certificate
  deriving Repr, DecidableEq

/-- A single kernelization observation over a compiled rule-layer artifact:
the artifact itself, the graph it reports, the graph the bounded extractor
finds as the effective decision surface, the source-derived edges the extractor
can justify within its bounded contract, and the capacity-aware extractor-run
vocabulary available at each block. The default extractor-run vocabulary is a
single clean unit run so existing non-capacity observations remain ordinary
kernelization observations unless a bridge overrides the capacity fields. -/
structure GovernanceKernelizationObservation
    (artifact : RuleLayerKernelArtifact) where
  reported : AuthorityGraph
  effective : AuthorityGraph
  sourceEdges : List AuthorityEdge
  reportedSemanticBridgeClean : Bool
  MessageAt : Nat → Type := fun _ => Unit
  inputAt : ∀ block, MessageAt block → ExtractorInput :=
    fun _ _ => artifact.src
  capabilityUsed : ∀ block, MessageAt block → Bool :=
    fun _ _ => true
  extractorOutput : ∀ block, MessageAt block → KernelizationExtractorBranch :=
    fun _ _ => KernelizationExtractorBranch.clean

/-- Every effective ordinary authority edge and override has bounded source
evidence. -/
def SourceEvidenceComplete
    {artifact : RuleLayerKernelArtifact}
    (observation : GovernanceKernelizationObservation artifact) : Prop :=
  ∀ edge : AuthorityEdge,
    HasAuthoritySurface observation.effective edge →
      SourceDerivesEdge observation.sourceEdges edge

noncomputable instance instDecidableSourceEvidenceComplete
    {artifact : RuleLayerKernelArtifact}
    (observation : GovernanceKernelizationObservation artifact) :
    Decidable (SourceEvidenceComplete observation) := by
  classical
  infer_instance

/-- Clean kernelization result: the report and effective authority surface are
extensionally equivalent, every effective edge is source-derived, and the
extracted runtime datum is a semantic legitimacy kernel. -/
def KernelizationClean
    {artifact : RuleLayerKernelArtifact}
    (observation : GovernanceKernelizationObservation artifact) : Prop :=
  AuthorityExtensionallyEquivalent observation.reported
      observation.effective ∧
    SourceEvidenceComplete observation ∧
      (artifact.extract artifact.src).IsSemanticKernel

noncomputable instance instDecidableKernelizationClean
    {artifact : RuleLayerKernelArtifact}
    (observation : GovernanceKernelizationObservation artifact) :
    Decidable (KernelizationClean observation) := by
  classical
  infer_instance

structure UnmodeledEdgeWitness
    {artifact : RuleLayerKernelArtifact}
    (observation : GovernanceKernelizationObservation artifact) where
  edge : AuthorityEdge
  effective_has_edge : HasAuthorityEdge observation.effective edge
  reported_lacks_edge : ¬ HasAuthorityEdge observation.reported edge

structure BypassPathWitness
    {artifact : RuleLayerKernelArtifact}
    (observation : GovernanceKernelizationObservation artifact) where
  source : AuthorityNodeId
  middle : List AuthorityNodeId
  target : AuthorityNodeId
  middle_nonempty : middle ≠ []
  route_nodup : (source :: middle ++ [target]).Nodup
  effective_route :
    AuthorityPathPermitted observation.effective
      (source :: middle ++ [target])
  reported_route :
    AuthorityPathPermitted observation.reported
      (source :: middle ++ [target])
  reported_lacks_direct :
    ¬ HasAuthorityEdge observation.reported
      { fromNode := source, toNode := target }

structure HiddenOverrideWitness
    {artifact : RuleLayerKernelArtifact}
    (observation : GovernanceKernelizationObservation artifact) where
  overrideEdge : AuthorityEdge
  dominatedPair : AuthorityEdge
  effective_has_override :
    HasAuthorityOverride observation.effective overrideEdge
  reported_lacks_override :
    ¬ HasAuthorityOverride observation.reported overrideEdge
  dominates_pair :
    overrideEdge.fromNode = dominatedPair.fromNode ∧
      overrideEdge.toNode = dominatedPair.toNode
  dominated_pair_reported :
    HasAuthorityEdge observation.reported dominatedPair

structure SourceEvidenceGapWitness
    {artifact : RuleLayerKernelArtifact}
    (observation : GovernanceKernelizationObservation artifact) where
  edge : AuthorityEdge
  effective_has_edge : HasAuthoritySurface observation.effective edge
  source_lacks_edge : ¬ SourceDerivesEdge observation.sourceEdges edge

structure SemanticBridgeFailureWitness
    {artifact : RuleLayerKernelArtifact}
    (observation : GovernanceKernelizationObservation artifact) where
  failure_locus : SemanticFailureLocus
  reported_semantic_bridge_clean :
    observation.reportedSemanticBridgeClean = true
  reported_clean_surface :
    AuthorityExtensionallyEquivalent observation.reported
      observation.effective ∧
      SourceEvidenceComplete observation
  source_wellFormed : artifact.src.WellFormed
  semantic_failure : ¬ (artifact.extract artifact.src).IsSemanticKernel

/-- The extractor output actually fails at the cited semantic-kernel locus. -/
def SemanticFailureLocusFails
    (artifact : RuleLayerKernelArtifact)
    (locus : SemanticFailureLocus) : Prop :=
  match locus with
  | SemanticFailureLocus.runtimeKernel =>
      ¬ IsLegitimacyKernel (artifact.extract artifact.src).data
  | SemanticFailureLocus.semanticBridge =>
      ¬ KernelSemanticBridge (artifact.extract artifact.src).data

/-- Strict structural ordering over semantic-kernel failure loci. -/
def SemanticFailureLocusPrecedes
    (earlier later : SemanticFailureLocus) : Prop :=
  match earlier, later with
  | SemanticFailureLocus.runtimeKernel, SemanticFailureLocus.semanticBridge =>
      True
  | _, _ => False

/-- A semantic failure locus is minimal when it fails and no earlier structural
semantic obligation fails. -/
def SemanticFailureLocusMinimal
    (artifact : RuleLayerKernelArtifact)
    (locus : SemanticFailureLocus) : Prop :=
  SemanticFailureLocusFails artifact locus ∧
    ∀ earlier : SemanticFailureLocus,
      SemanticFailureLocusPrecedes earlier locus →
        ¬ SemanticFailureLocusFails artifact earlier

lemma semanticFailureLocusMinimal_not_semantic
    {artifact : RuleLayerKernelArtifact}
    {locus : SemanticFailureLocus}
    (hminimal : SemanticFailureLocusMinimal artifact locus) :
    ¬ (artifact.extract artifact.src).IsSemanticKernel := by
  intro hsemantic
  cases locus with
  | runtimeKernel =>
      exact hminimal.1 hsemantic.runtimeKernel
  | semanticBridge =>
      exact hminimal.1 hsemantic.semanticBridge

/-- Hidden-authority certificates are concrete witnesses, one constructor per
discrepancy class. -/
inductive HiddenAuthorityCertificate
    {artifact : RuleLayerKernelArtifact}
    (observation : GovernanceKernelizationObservation artifact) where
  | unmodeledEdge :
      UnmodeledEdgeWitness observation → HiddenAuthorityCertificate observation
  | bypassPath :
      BypassPathWitness observation → HiddenAuthorityCertificate observation
  | hiddenOverride :
      HiddenOverrideWitness observation → HiddenAuthorityCertificate observation
  | sourceEvidenceGap :
      SourceEvidenceGapWitness observation → HiddenAuthorityCertificate observation
  | semanticBridgeFailure :
      SemanticBridgeFailureWitness observation →
        HiddenAuthorityCertificate observation

/-- A bypass witness is minimal when the reported route is a genuine permitted
bypass and no proper subroute is itself a permitted bypass. -/
def BypassPathMinimal
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (graph : AuthorityGraph)
    (witness : BypassPathWitness observation) : Prop :=
  let route := witness.source :: witness.middle ++ [witness.target]
  IsEdgePermittedRoute graph route ∧
    IsEdgePermittedBypass graph route ∧
      ∀ shorter : List AuthorityNodeId,
        ProperRouteSublist shorter route →
          ¬ IsEdgePermittedBypass graph shorter

/-- A hidden override dominates the structurally named ordinary authority pair
with the same endpoints. -/
def HiddenOverrideDominatesPair
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (witness : HiddenOverrideWitness observation) : Prop :=
  witness.overrideEdge.fromNode = witness.dominatedPair.fromNode ∧
    witness.overrideEdge.toNode = witness.dominatedPair.toNode ∧
      HasAuthorityEdge observation.reported witness.dominatedPair

/-- Minimality predicate for emitted certificates. The load-bearing clauses use
computed edge/override differences, proper-subroute exclusion, source derivation
failure, and observation-indexed semantic-bridge failure rather than replaying
the constructor fields. -/
def MinimalHiddenAuthority
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (cert : HiddenAuthorityCertificate observation) : Prop :=
  match cert with
  | HiddenAuthorityCertificate.unmodeledEdge witness =>
      witness.edge ∈ AuthorityEdgeDifference observation.effective
        observation.reported
  | HiddenAuthorityCertificate.bypassPath witness =>
      witness.middle ≠ [] ∧
        (witness.source :: witness.middle ++ [witness.target]).Nodup ∧
          IsEdgePermittedRoute observation.effective
            (witness.source :: witness.middle ++ [witness.target]) ∧
            BypassPathMinimal observation.reported witness
  | HiddenAuthorityCertificate.hiddenOverride witness =>
      witness.overrideEdge ∈
          AuthorityOverrideDifference observation.effective
            observation.reported ∧
        HiddenOverrideDominatesPair witness
  | HiddenAuthorityCertificate.sourceEvidenceGap witness =>
      HasAuthoritySurface observation.effective witness.edge ∧
        ¬ SourceEvidenceDerivable observation.sourceEdges witness.edge
  | HiddenAuthorityCertificate.semanticBridgeFailure witness =>
      observation.reportedSemanticBridgeClean = true ∧
        artifact.src.WellFormed ∧
          SemanticFailureLocusMinimal artifact witness.failure_locus

noncomputable instance instDecidableMinimalHiddenAuthority
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (cert : HiddenAuthorityCertificate observation) :
    Decidable (MinimalHiddenAuthority cert) := by
  classical
  infer_instance

theorem semanticBridgeFailure_minimal_incompatible_clean
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (witness : SemanticBridgeFailureWitness observation)
    (hminimal :
      MinimalHiddenAuthority
        (HiddenAuthorityCertificate.semanticBridgeFailure witness)) :
    ¬ KernelizationClean observation := by
  intro hclean
  exact semanticFailureLocusMinimal_not_semantic hminimal.2.2 hclean.2.2

/-- Kernelization honesty: either the kernelization observation is clean or
there is a minimal hidden-authority certificate. -/
def KernelizationHonesty
    {artifact : RuleLayerKernelArtifact}
    (observation : GovernanceKernelizationObservation artifact) : Prop :=
  KernelizationClean observation ∨
    ∃ cert : HiddenAuthorityCertificate observation,
      MinimalHiddenAuthority cert

/-- Concrete clean witness emitted by a kernelization extractor. It carries the
component witnesses used to build `KernelizationClean`; it is not itself a
wrapper around the final honesty disjunction. -/
structure KernelizationCleanWitness
    {artifact : RuleLayerKernelArtifact}
    (observation : GovernanceKernelizationObservation artifact) where
  input : ExtractorInput
  reported_equiv :
    AuthorityExtensionallyEquivalent observation.reported
      observation.effective
  source_complete : SourceEvidenceComplete observation
  semantic_kernel : (artifact.extract artifact.src).IsSemanticKernel

lemma kernelizationClean_of_witness
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (witness : KernelizationCleanWitness observation) :
    KernelizationClean observation :=
  ⟨witness.reported_equiv, witness.source_complete,
    witness.semantic_kernel⟩

/-- Contract supplied by a bounded kernelization extractor. The contract is
function-shaped: it exposes an extraction function and branch soundness. None of
its fields is the final honesty disjunction. -/
structure KernelizationExtractorContract
    {artifact : RuleLayerKernelArtifact}
    (observation : GovernanceKernelizationObservation artifact) where
  extract :
    ExtractorInput →
      Sum (KernelizationCleanWitness observation)
        (HiddenAuthorityCertificate observation)
  cleanSound :
    ∀ input witness,
      extract input = Sum.inl witness →
        KernelizationClean observation
  certSound :
    ∀ input cert,
      extract input = Sum.inr cert →
        MinimalHiddenAuthority cert

lemma kernelizationHonesty_from_cleanSound
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (contract : KernelizationExtractorContract observation)
    (input : ExtractorInput)
    (witness : KernelizationCleanWitness observation)
    (hextract : contract.extract input = Sum.inl witness) :
    KernelizationHonesty observation :=
  Or.inl (contract.cleanSound input witness hextract)

lemma kernelizationHonesty_from_certSound
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (contract : KernelizationExtractorContract observation)
    (input : ExtractorInput)
    (cert : HiddenAuthorityCertificate observation)
    (hextract : contract.extract input = Sum.inr cert) :
    KernelizationHonesty observation :=
  Or.inr ⟨cert, contract.certSound input cert hextract⟩

lemma kernelizationHonesty_from_extractorResult
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (contract : KernelizationExtractorContract observation)
    (input : ExtractorInput)
    {result :
      Sum (KernelizationCleanWitness observation)
        (HiddenAuthorityCertificate observation)}
    (hextract : contract.extract input = result) :
    KernelizationHonesty observation := by
  cases result with
  | inl witness =>
      exact kernelizationHonesty_from_cleanSound contract input witness
        hextract
  | inr cert =>
      exact kernelizationHonesty_from_certSound contract input cert
        hextract

/-- Kernelization-honesty theorem for compiled governance artifacts. Under the
bounded kernelization extractor contract, the artifact either governs as the
reported surface claims or the extractor emits a minimal hidden-authority
certificate. -/
theorem kernelization_honesty
    (artifact : RuleLayerKernelArtifact)
    (observation : GovernanceKernelizationObservation artifact)
    (contract : KernelizationExtractorContract observation) :
    KernelizationHonesty observation := by
  match hresult : contract.extract artifact.src with
  | Sum.inl witness =>
      exact kernelizationHonesty_from_cleanSound contract artifact.src
        witness hresult
  | Sum.inr cert =>
      exact kernelizationHonesty_from_certSound contract artifact.src
        cert hresult

end Safety

end Legitimacy
