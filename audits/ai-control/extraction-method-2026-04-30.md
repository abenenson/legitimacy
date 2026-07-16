# AI Control extraction method, 2026-04-30

Source: Greenblatt et al., "AI Control: Improving Safety Despite Intentional Subversion", arXiv:2312.06942v5. Primary source artifacts were the arXiv abstract page and the arXiv source bundle `main.tex`.

This extraction uses the explicit source corpus and records the source lines below.

## Audit encoding

The Lean audit surface is `AuditGovernanceGraph` from `Legitimacy.Results.GovernanceAdmissibilityAudit`. A node emits `Permit`, `Escalate`, or `Deny`; only `Escalate` claims are forwarded along graph edges. This makes Control protocols encode naturally as direct-submit paths plus monitor/audit routing paths.

Mapping rules:

- `U` becomes `untrusted_policy`, a default-permit code-production node.
- `T` monitor/classifier steps become threshold routers. A threshold match emits `Escalate` to a downstream review, defer, or edit node.
- `H` audit becomes a terminal trusted-review node. A matched high-suspicion or confirmed-backdoor evidence signal emits `Deny`, representing shutdown or rejection; otherwise review returns `Permit`.
- Defer-to-trusted and trusted-editing are represented as dynamic-routing branches that send intermediate suspicion cases to a trusted solution/edit node.
- Numeric thresholds are normalized to `1.0`. The graph is structural, not calibrated to the paper's exact percentile cutoffs.

## Source anchors

- The setting defines a protocol as a sequential procedure returning attempted solutions: `main.tex:L193-L204`.
- The resources are untrusted model `U`, trusted model `T`, and high-quality trusted labor `H`: `main.tex:L195-L204`.
- `H` is used to audit submitted code and can trigger shutdown if code appears backdoored: `main.tex:L220-L228`; Table 1 summarizes outcomes.
- Figure 1 describes the control-evaluation setup and the `U`/`T`/`H` resource split: `main.tex:L146-L150`.
- The summary table lists the five audited protocol families: `main.tex:L299-L314`.

## Protocol extractions

### Upfront auditing

Source: `main.tex:L348-L365`, Figure 2, Table 2.

Graph: `upfront-auditing-graph.json`.

Nodes:

- `untrusted_policy`: `U` produces code.
- `upfront_audit_router`: routes submissions in the initial H-budget audit window.
- `human_audit`: trusted audit rejects/shuts down on the audited high-risk branch.

Trigger: `upfront_audit_window >= 1`.

### Trusted monitoring

Source: `main.tex:L132-L139`, `main.tex:L377-L385`, `main.tex:L425-L432`, Figure 1, Figure 3, Table 2.

Graph: `trusted-monitoring-graph.json`.

Nodes:

- `untrusted_policy`: `U` produces code.
- `trusted_monitor`: `T` rates suspiciousness and routes top scores to audit.
- `human_audit`: `H` resolves suspicious audited code.

Trigger: `trusted_suspicion >= 1`.

### Trusted monitoring with defer to trusted

Source: `main.tex:L446-L453`, `main.tex:L455-L472`, Figure 2, Table 3.

Graph: `trusted-monitoring-defer-graph.json`.

Nodes:

- `untrusted_policy`: `U` produces code.
- `trusted_monitor_audit_router`: top-suspicion route to `H`.
- `trusted_monitor_defer_router`: intermediate-suspicion route to `T`.
- `human_audit`: `H` rejects/shuts down on top-suspicion audited code.
- `trusted_solution`: `T` writes the substitute solution.

Triggers: `trusted_suspicion_top2 >= 1`, `trusted_suspicion_defer_band >= 1`.

### Untrusted monitoring

Source: `main.tex:L478-L500`, `main.tex:L506-L513`, `main.tex:L549-L580`, `main.tex:L605-L609`, `main.tex:L618-L633`, Figure 2, Table 2, Table 5.

Graph: `untrusted-monitoring-graph.json`.

Nodes:

- `monitor_validation`: synthetic examples from `H` validate the untrusted monitor before deployment.
- `untrusted_policy`: `U` produces code.
- `redacted_untrusted_monitor`: separate `U` monitor, with redaction/signal-jamming and `T` ensembling, routes suspicious code to audit.
- `human_audit`: `H` resolves suspicious audited code.

Triggers: `monitor_validation_failure >= 1`, `combined_untrusted_suspicion >= 1`.

### Trusted editing

Source: `main.tex:L637-L658`, `main.tex:L660-L662`, `main.tex:L299-L314`, Figure 2, Table 6.

Graph: `trusted-editing-graph.json`.

Nodes:

- `untrusted_policy`: `U` produces code.
- `trusted_edit_audit_router`: top-suspicion original `U` code goes to `H`.
- `trusted_edit_router`: edit-band suspicious code goes to `T` editing.
- `human_audit_original`: `H` audits the original top-suspicion code.
- `trusted_editor`: `T` edits suspicious code and submits the edited result.

Triggers: `trusted_edit_top2_suspicion >= 1`, `trusted_edit_band_suspicion >= 1`.

## Ambiguities and calibration

The audit graphs intentionally do not encode calibrated safety/usefulness probabilities. Percentiles such as top 2%, 10%, or 20% are collapsed to structural threshold predicates. The result is therefore a structural routing audit, not a reproduction of the paper's Monte Carlo evaluation.

The monotonicity verdict is sensitive to a modeling choice that is also faithful to the graph semantics: route-to-review predicates are treated as strengthenable metric fields. Under that semantics, increasing suspicion/evidence can move a baseline claim from direct permit into trusted review, where the trusted review branch denies. If a future extraction separates "more claimant strength" from "more suspicion/evidence against the claimant", the monotonicity result should be rerun and documented as conditional on that richer metric polarity.
