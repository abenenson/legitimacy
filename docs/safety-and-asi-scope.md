# Safety And ASI Scope

This page preserves the safety and safety-scope material moved out of the root README. Return to the concise entry point at [README.md](../README.md), or use [repository-context.md](repository-context.md) for the full theorem map.

## Scope Notes

The safety claim is deliberately structural. `legitimacy` does not prove that an arbitrary agent is aligned, corrigible, or safe; it proves and executes a narrower discipline at the rule layer.

For increasingly capable systems this matters because local policy checks are not enough. A governance mechanism can remain executable while losing observability, compositional safety, corrigibility, or non-vacuity under scale, composition, or self-modification pressure. The safety stack is designed to make that degradation non-silent. `noUndeclaredSacrifice` is a static activation gate: a rule whose forced consistency or monotonicity sacrifice is not declared cannot be promoted to the live state. `kernelReachabilitySafety` is a dynamic trajectory gate for `KernelGovernedTrajectory`, and `stateful_agent_schedule_safety` extends the same gate to covered stateful schedules: reachable states remain invariant or surface an indexed monitored sacrifice certificate. The detailed mapping from these pressures to formal interfaces lives in [`docs/repository-context.md`](repository-context.md).

The scaling-pressure material is structural, not universal. The repository packages spectral universality, the Stackelberg capability-pressure limit in the spectral surrogate, the critical-capability phase transition, and scope-qualified corrigibility bridges; it does not claim a universal reliability theorem. A scoped kernel bridge, retaining the existing Lean `ASIBridge` naming, is proved for family-aligned kernel data currently inhabited by uniK5, uniK7, and uniK9 carriers; the n=7/n=9 size-indexed signature witnesses are `uniK7_asiSpectralSignature_depth3` and `uniK9_asiSpectralSignature_depth3`, and the carrier-specific kernel-invariant bridges are `uniK7_family_aligned_native_asi_signature_kernelInvariant` and `uniK9_family_aligned_native_asi_signature_kernelInvariant`. A substrate-wide free bridge remains open. Constitutional AI has a narrow deployment-side audit-subject lineage bridge (`ConstitutionalAITrainedAuditSubject`, `spectralBehavioralEmbedding`, `constitutionalAI_zero_consistency_vulnerability_implies_game_strategyproof`), not a full embedding of Anthropic Constitutional AI; deliberative alignment remains outside that CAI embedding. A narrow typed AI Control protocol-role projection exists (`AIControlGovernanceGraph`, `MonitorCapacityLineage`, `declared_escalation_yields_monitored_sacrifice`); full behavioral/evaluation embedding of AI Control results remains future work. Nor are the per-harness verdicts a ranking of project legitimacy or a social endorsement mechanism — they are structural diagnostic outputs, not value judgments about the projects themselves.


## Related Context

The detailed theorem-by-theorem map is in [repository-context.md](repository-context.md). The formal/executable boundary is in [boundary.md](boundary.md).
