# Constructive Decidable Frontier

`instDecidableMinimalHiddenAuthority` remains classical in Lean because the
semantic-bridge certificate branch depends on propositions over extracted
kernel data:

- `IsLegitimacyKernel (artifact.extract artifact.src).data`
- `KernelSemanticBridge (artifact.extract artifact.src).data`

Those predicates quantify over kernel-side semantic obligations rather than the
finite authority lists that Rust enumerates. The finite structural branches are
constructive in the Rust validator: edge difference, override difference,
proper-route sublist exclusion, source-edge membership, and the ordered
semantic failure locus are all computed over bounded data. The current Lean
floor is classical only where the artifact exposes an arbitrary
`KernelExtractor` and arbitrary semantic kernel predicates.

A constructive restricted instance is available for the Rust mirror class:
observations whose authority graphs and source evidence are finite lists, and
whose semantic-kernel verdicts are supplied by a bounded checker. That is the
class enforced by `RuleLayerKernelArtifact::verify` and
`minimal_hidden_authority` in Rust; it does not compute through the general Lean
semantic predicates.
