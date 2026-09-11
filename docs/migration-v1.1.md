# Migrating from Legitimacy 1.0 to 1.1

The v1.1 research release uses package version 1.1.1. It adds the
executed-composition artifact and corrects cases where audit output claimed
more evidence than was available. **This release includes breaking changes
to the public Rust API and JSON contract.** Its minor release number is not
a promise of backward compatibility with v1.0.0. Update consumers using the
migration inventory below. The finite experiment does not certify deployed
agents or establish a general empirical capability threshold.

The earlier v1.1.0 release was withdrawn. Its version identifier is not reused
for the 1.1.1 candidate. Use the current published release or a specifically
identified checkout; do not treat a withdrawn artifact as the current release.

## Rust boundary assessments

`BoundaryCausalSafetyAssessment` is now an enum. An assessment may be
`Unassessed { reason }` or `Assessed { summary, affected_governance_nodes,
external_dependency_count, ungoverned_dependencies }`. This changes struct
construction and field access, including through extraction and audit results.

Callers can match the variants or use the accessor methods:

```rust
use legitimacy::BoundaryCausalSafetyAssessment;

fn report_boundary(assessment: &BoundaryCausalSafetyAssessment) {
    match assessment {
        BoundaryCausalSafetyAssessment::Unassessed { reason } => {
            println!("Boundary not assessed: {reason}");
        }
        BoundaryCausalSafetyAssessment::Assessed {
            external_dependency_count,
            ..
        } => {
            println!("Observed external dependencies: {external_dependency_count}");
        }
    }
}
```

`summary()` returns the assessment summary or unassessed reason.
`affected_governance_nodes()`, `external_dependency_count()` and
`ungoverned_dependencies()` return `Option` values. `None` means the analysis was
not performed. Do not convert it to zero or an empty list and report those as
measurements. The default is unassessed. A graph alone cannot establish that
source dependencies are absent or that source-level LIVE readiness is satisfied.

## JSON consumers

| Surface | Migration |
| --- | --- |
| Boundary assessment | Branch on `status: "assessed"` or `"unassessed"`. An unassessed object contains `reason` and omits measured counts/dependencies. Assessed objects retain those fields. |
| Graph-only coverage | Expect `complete: false` when loading a graph without source evidence. Preserve the source-level readiness blocker. |
| `activation_gate.required_certificate_format` | Accept `null` when no supported sacrifice certificate is required. Use `required_certificates` for the complete list of actual required sacrifices. |
| Activation state | Handle `compiled_without_sacrifice`, `requires_declared_sacrifice` and `compilation_failed`; inspect the compiler result instead of assuming every graph requires a sacrifice. |
| Replay `provenance.source_path` | Treat `embedded:` values as provenance identifiers, not paths to open. Fixture replay uses immutable bytes embedded in the binary. |
| Divergent extracted graphs | Do not infer fixture theorem coverage from the target name. An unmatched graph can report `extracted_graph_rejected` with graph-level feature names and a null `repaired_alternative`. |

The [audit bundle contract](audit-bundle-schema.md) describes these fields and
examples. The [extraction boundary](extractor-boundary.md) explains where a
fixture theorem applies. Signatures authenticate bytes relative to a trust
policy; they do not independently establish the truth or completeness of a
capture or the authority to perform an action.

## Corrected numeric behavior

Certificates reject nonfinite values and overflowing outcome comparisons.
Allocation feasibility rejects nonfinite total allocations. Proportional
allocation handles extreme finite strengths without overflow; evaluation-order
changes may also change last-bit rounding. Consumers must handle rejected
invalid inputs rather than depend on the earlier approvals.

## Commands, formats and provenance

Existing CLI commands remain available. The new executed-composition command
and trajectory tools are additions. The package version is independent of
`v0`/`v1` in schema names and file paths; those identify wire formats and are not
renamed merely because the package version changes.

Source-bound capture receipts remain tied to their recorded producer. A package
or selected-build-input change does not authorize rewriting old captures,
substituting source hashes, or admitting a receipt from another producer. Build
new evidence through the existing capture path when needed and retain historical
receipts as historical evidence. Linux qualification does not imply support for
Linux-specific capture operations on other platforms.
