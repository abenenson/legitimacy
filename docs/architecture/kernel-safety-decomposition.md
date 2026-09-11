# Kernel Safety Module Decomposition

## Responsibility boundaries

1. `KernelSafety.Core`: semantic kernel invariant vocabulary, governed graph projection,
   certified kernel transitions, and direct invariant preservation.
2. `KernelSafety.Sacrifice`: sacrificed obligations, kernel-axiom violations,
   monitored sacrifice obligations, aggregator witness tags, stateful
   critical-capability violations, and first-class monitored sacrifice
   certificates.
3. `KernelSafety.Trajectory`: finite kernel-governed trajectories, one-step
   constructors, invariant-only trajectories, and the embedding into full
   trajectories.
4. `KernelSafety.BinaryDecisionPipeline`: no-undeclared-sacrifice theorems for
   binary-pipeline live surfaces, bounded stateful corrigibility preservation,
   aggregator-witnessed sacrifice predicates, and the stateful
   bounded-corrigibility-or-sacrifice disjunction.
5. `KernelSafety.ReachabilityStack`: reachable-state safety, schedule-to-kernel
   extraction frontier, extracted-kernel semantic transfer, stateful sidecar
   proposition, empirical parity sidecar, and the unified all-branches safety
   theorem.
6. `KernelSafety.GovernanceExamples`: concrete five-node governance datum,
   widened-signal mutation, action-driven threshold mutation, and basic
   kernel-governed trajectories.
7. `KernelSafety.StatefulExamples`: import-stable umbrella for the nested
   stateful worked-example split. `StatefulExamples.Conclusions` owns shared
   safety conclusions, `ConcreteAdversaries` owns concrete stateful adversary
   inhabitants, `ExtractorArtifacts` owns extractor fixtures,
   `ConsistencySacrifice` owns the supercritical sacrifice-route example, and
   `ScheduleExtraction` owns worked schedule-extraction instantiations.

## Dependency graph

`Core` imports the current kernel, protocol, stateful-adversary, spectral,
extractor, and impossibility surfaces needed by kernel transitions.

`Sacrifice` imports `Core`.

`Trajectory` imports `Sacrifice`.

`BinaryDecisionPipeline` imports `Sacrifice`; it does not depend on trajectory
definitions.

`ReachabilityStack` imports `Trajectory`, `BinaryDecisionPipeline`, and
`Legitimacy.Extract.Soundness`.

`GovernanceExamples` imports `ReachabilityStack`.

`StatefulExamples.Conclusions` imports `GovernanceExamples`; the sibling
stateful-example modules build on `Conclusions`, and the
`StatefulExamples` umbrella re-exports the nested split.

The umbrella `Legitimacy.Safety.KernelSafety` imports all submodules and
contains no declarations except the final architecture docstring, preserving
existing downstream import compatibility.

## Re-export shape

Existing downstream callers import `Legitimacy.Safety.KernelSafety`. The
umbrella file will continue to expose the full public surface by importing:

- `Legitimacy.Safety.KernelSafety.Core`
- `Legitimacy.Safety.KernelSafety.Sacrifice`
- `Legitimacy.Safety.KernelSafety.Trajectory`
- `Legitimacy.Safety.KernelSafety.BinaryDecisionPipeline`
- `Legitimacy.Safety.KernelSafety.ReachabilityStack`
- `Legitimacy.Safety.KernelSafety.GovernanceExamples`
- `Legitimacy.Safety.KernelSafety.StatefulExamples`

`StatefulExamples` is itself an umbrella and re-exports:

- `Legitimacy.Safety.KernelSafety.StatefulExamples.Conclusions`
- `Legitimacy.Safety.KernelSafety.StatefulExamples.ConcreteAdversaries`
- `Legitimacy.Safety.KernelSafety.StatefulExamples.ExtractorArtifacts`
- `Legitimacy.Safety.KernelSafety.StatefulExamples.ConsistencySacrifice`
- `Legitimacy.Safety.KernelSafety.StatefulExamples.ScheduleExtraction`

The public surface preserved through the umbrella includes the current
transition vocabulary, sacrifice certificates, trajectory constructors,
pipeline safety theorems, reachable-state and extracted-stack statements, and
worked examples.

## Cross-file rename surface

No public Lean declarations need to be renamed for the extraction. Existing
names are content-oriented in their new homes: `KernelStep`,
`MonitoredSacrificeCertificate`, `KernelGovernedTrajectory`,
`binaryDecisionPipeline_noUndeclaredSacrifice`,
`statefulAdversary_via_consistencyWitnessedAggregator_yields_boundedCorrigibility_or_sacrifice`,
`extractedKernelData_satisfies_boundedSafetyStack`, and the worked-example
names remain accurate. Module names are functional and avoid internal process
vocabulary.

### Architecture docstring sketch

The final umbrella docstring should describe `KernelSafety` as an import-stable
facade over seven submodules. It should direct maintainers to add semantic
transition vocabulary to `Core`, monitored sacrifice protocol to `Sacrifice`,
finite execution structure to `Trajectory`, binary-pipeline and stateful
obstruction bridges to `BinaryDecisionPipeline`, bounded-stack theorem packaging
to `ReachabilityStack`, base governance fixtures to `GovernanceExamples`, and
stateful/extractor worked instantiations to the nested `StatefulExamples`
children, with `StatefulExamples` remaining a re-export umbrella. It should
also state the intended dependency order and warn against placing new proof
content in the umbrella.

## Compiled Claim Policy And Action Boundary

`Legitimacy.Protocol.CompiledStepPolicy` owns the canonical claim-native
decision seam. Its state is `List ClaimQ`, its local action is `ClaimQ`, and
`CompiledGovernance.appendClaim` preserves source order. Singleton local
decisions and accumulated-profile denial both evaluate
`graphDecide compiled.graph`; `CompiledGovernance` stores no policy function.
The peer-graph fixtures prove both a benign two-claim profile and an inhabited
three-claim `ClaimDecompositionAttack` over an existing compiled artifact.

`Legitimacy.Bridges.DecompositionAttackKernelBridge` is only a conditional
monitor-retag layer. It accepts an already-emitted
`MonitoredSacrificeCertificate` plus the certificate's canonical compiled
claim attack. It does not derive monitor evidence, bind claims to kernel
actions, or prove `KernelAxiomViolation`.

The dependent trajectory milestone must bind one exact nonempty action trace:
an `encodeAction : D.actionSpace.Action → ClaimQ` maps
`step.action_trace`, and all graph facts range over exactly
`step.action_trace.map encodeAction`. This supplies syntactic order and length
binding. Semantic replay still requires either a concrete claim action space
with a proved law or an explicit action/claim simulation premise.

## Kernel Trajectory And Stateful Schedule Boundary

`TransitionSequence`, `applyStatefulTrajectory`, and
`KernelGovernedTrajectory` model three different boundaries.

`TransitionSequence` is the protocol lifecycle closure over
`ProtocolState`. It records declarations, compilation, measurement, live
deployment, supervision, drift, and recompilation. Its live conclusion is used
by the binary-pipeline sacrifice theorems through `protocol_live_soundness`:
a live compiled artifact exposes the non-sacrificed property facts, justified
sacrifice list, and calibrated risk report needed to reject undeclared
consistency or monotonicity sacrifice.

`applyStatefulTrajectory` is a stateful schedule executor over one fixed
`LegitimacyKernelData` datum. Kernel schedule steps apply actions to the
runtime `GovernanceState`; adversary schedule steps update adversary memory and
the runtime state after observing the kernel response. The executor returns a
`StatefulAdversaryConfig`; it does not emit a new `LegitimacyKernelData`, a
`KernelStep`, or a monitored sacrifice certificate.

`KernelGovernedTrajectory` is the reachable-kernel proof object over
`LegitimacyKernelData`. Each transition is either a certified invariant step or
a monitored sacrifice step. Reachable-state safety consumes this proof object
directly.

Consequently there is no non-vacuous theorem deriving a
`KernelGovernedTrajectory` from a live `TransitionSequence` plus a stateful
schedule alone. `kernelGovernedTrajectory_schedule_extraction_contract` is the
named frontier theorem: it proves that the bridge closes exactly when supplied
with `ScheduleKernelExtraction`, a per-step contract carrying the target kernel
datum and either a `KernelStep` proof for invariant transitions or a
`MonitoredSacrificeCertificate` for sacrifice transitions. The theorem returns
`Nonempty (KernelGovernedTrajectory ...)` because the trajectory itself is proof
data in `Type`, while the conversion function exposes the concrete witness.
Bundling the existing live-path, stateful-corrigibility, and
governed-trajectory hypotheses together would be only a conjunction and would
not remove an independent assumption.

The current stack therefore keeps the layers separate: protocol live reachability
authorizes compiled-property sacrifice certificates in
`BinaryDecisionPipeline`; stateful schedules prove bounded corrigibility or a
critical-budget sacrifice sidecar; kernel reachability proves safety from an
explicit `KernelGovernedTrajectory`.
`extractedKernelData_satisfies_allBranchesKernelGovernanceSafety` consumes the
live compiled surface for the stateful disjunction and an explicit governed
trajectory for the kernel disjunction.

## Unified Safety Surface Audit

Bridge verdict: the schedule-to-kernel bridge is not derivable from the current
data. A live `TransitionSequence` exposes compiled-governance soundness, and
`applyStatefulTrajectory` exposes the final adversary configuration and realized
proposal budget. Neither surface names the target `LegitimacyKernelData` for
each schedule step, proves a `KernelStep` for invariant transitions, or emits a
`MonitoredSacrificeCertificate` for sacrifice transitions. The bridge can be
closed by a first-class extraction contract carrying exactly those per-step
kernel-transition witnesses.

Unified theorem shape: the headline theorem consumes a bounded extractor
contract, well-formed source input, semantic transfer from extracted datum to
live datum, an explicit `KernelGovernedTrajectory`, a live compiled surface, the
binary consistency witness data, and a stateful schedule. Its conclusion is one
proposition:
`(KernelInvariant D' ∨ KernelTrajectoryHasSacrifice h_traj) ∧
StatefulCorrigibilityOrConsistencySacrifice ...`, with extractor parity kept as
the fixture sidecar where parity inputs are supplied. The first conjunct must be
derived by semantic transfer plus `reachable_state_safety`, preserving the
path-indexed sacrifice witness inside `KernelTrajectoryHasSacrifice`; the second
conjunct must be derived by the stateful adversary theorem, not accepted as an
already-packaged disjunction.

Sacrifice-branch example shape: the headline right-branch worked example should
use `lengthThreeSurvivorKernelData` and `exampleSupercriticalAdversary`. The
kernel-reachability axis should construct a one-step
`KernelGovernedTrajectory.sacrifice_step` from the concrete consistency
certificate returned by
`exampleSupercriticalAdversary_yields_consistency_sacrifice_right`, yielding
`KernelGovernedTrajectory.HasSacrificeStepAt ... 0`. The stateful axis should
reuse the same theorem's right disjunct, which carries concrete claim-profile,
claimant, consistency-witness tag, and the stateful critical-capability
violation.
