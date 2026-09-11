# Protocol state trust contract

The `legitimacy protocol` CLI operates on trusted operator-local JSON
checkpoints. These files are not signed certificates and are not a supported
untrusted submission format. Keep the source graph, representative claims and
checkpoint files under the operator's control.

`protocol init` evaluates the supplied graph and rejects undeclared violations.
`protocol measure` evaluates the graph with representative claims and computes
the risk report. Later transitions validate state structure and selected
cross-field relationships; `protocol activate` does not rerun measurement or
authenticate the checkpoint's origin.

The compiled-rule hash binds the supplied graph, synthetic claims, axiom
verdicts and strategyproofness result. It is an unkeyed hash: it detects a
change without a matching hash update, but anyone replacing a file can also
recompute its hash. Declaration and risk-report numbers are not included in
that compiled-rule hash. Range checks and equality between duplicated exposure
fields do not establish that the values were computed from the graph.

Consequently, changing finite declaration `spectral_gap` or `cv_bound` values
can survive activation; changing consistent risk-report values can affect
monitor interval selection. Do not use an imported checkpoint as independent
evidence of those measurements. Start from reviewed graph and claim inputs and
rerun initialization and measurement locally when provenance is uncertain.

`protocol audit` verifies the internal linkage and head of the checkpoint's
certificate chain. `certificate_chain_valid: true` is true for an empty,
consistent chain too. It does not certify measurement correctness, the truth
of a declared policy, checkpoint authenticity, or completeness of a history
against an external anchor. A party able to replace the entire checkpoint can
replace a chain with another internally consistent one.

This contract is separate from the signed executed-composition capture format.
That format checks a receipt against an independently selected trust policy
and recomputes its finite experiment semantics; even there, capture signatures
do not prove that a trusted host reported reality honestly. See
[executed-composition evidence boundaries](executed-composition-v1.md).

The Lean kernel statements are claims under their stated typed hypotheses.
Loading a Rust protocol checkpoint does not supply machine-checked proofs of
those hypotheses for an arbitrary deployment.
