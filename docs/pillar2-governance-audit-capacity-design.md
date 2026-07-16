# Pillar 2 governance audit capacity design

## Outcome

The capacity layer is a standalone finite-Shannon-capacity contribution.  A
non-circular theorem deriving the real governance-admissibility verdict from
channel capacity does not exist in the current substrate.

The structural reason is explicit in Lean:

- `CapacityAchievingPrior K.channel p` depends only on the stochastic kernel and
  prior.
- `governanceAdmissibilityVerdict subject = AuditVerdict.legitimate` depends
  only on the extracted audit graph and evaluator.
- No object maps channel reports into the audit graph's claim corpus,
  nonvacuity witness, or per-check evidence.

Because the channel and verdict are independent parameters, any universal
capacity-to-admissibility bridge can be refuted by pairing a capacity-achieving
channel with a non-legitimate audit subject.

## Independent Legitimacy

`IndependentAuditAllocationLegitimate subject K p` is the independent predicate
used by `GovernanceAuditCapacity.lean`.  It contains:

1. `AuditSubjectAdmissible subject`, defined as the real theorem-facing
   `governanceAdmissibilityVerdict subject = AuditVerdict.legitimate`.
2. `AuditPriorReportable K p`, a kernel-side atomic reportability condition.

It deliberately contains no `CapacityAchievingPrior` field.  It can fail because
the real audit verdict is rejected or undischarged, as in
`cyclicSkippedAuditGraph_not_legitimate`, or because the reporting kernel has a
non-atomic output row.

## Orthogonality Witnesses

`concrete_capacity_achieving_prior_not_independent_legitimate_for_cyclic_skipped_graph`
exhibits a capacity-achieving prior for the concrete BSC audit channel while
independent legitimacy fails on `cyclicSkippedAuditGraph`.

`concrete_independent_legitimate_prior_not_capacity_achieving` exhibits a
reportable prior for the legitimate `compilerAuditGraph` that is not
capacity-achieving.  The proof uses the finite strict-concavity uniqueness
theorem to show that the two point-mass priors cannot both be capacity
achievers.

The two explicit refutations,
`no_universal_capacity_to_independent_legitimacy_bridge` and
`no_universal_independent_legitimacy_to_capacity_bridge`, record that neither
direction is valid in this substrate.

## Reportability

Reportability is now a proved kernel fact, not a field in a semantic bundle.
`auditPriorReportable_of_finite_output` proves reportability for finite atomic
output alphabets.  The compatibility theorem
`reportable_of_capacity_for_finite_output` accepts a capacity-achievement
hypothesis only because old call sites may have it; the proof does not use it.

The counterexample
`capacity_achieving_not_reportable_nonAtomicUnitInterval` shows why no
unrestricted `reportable_of_capacity` theorem is sound: the unit-input channel
with unit-interval Lebesgue output has a capacity-achieving prior, but no
singleton report has positive probability.

## Capacity Contribution

The concrete BSC channel at noise `1/4` remains a genuine Shannon-capacity
witness.  Its capacity is computed from the channel kernel alone by
`concreteQuarterNoisyAuditChannel_capacity_eq_log_two_sub_binEntropy`, and
`concreteQuarterNoisyAuditChannel_capacity_lt_one` proves the independent
capacity bound using the closed-form BSC theorem and analytic bounds on
`log 2`.
