# Governance Decision Lattice

Extractor lanes must normalize source-level governance outcomes into one
canonical graph decision lattice before monotonicity, parity, or cross-harness
checks compare verdicts.

## Canonical Decisions

The graph decision lattice has three decisions:

- `Permit`: the source policy authorizes the action without further authority.
- `Deny`: the source policy rejects the action.
- `Escalate`: the source policy does not authorize the action locally and
  delegates the verdict to a higher authority or later review.

`Deny` is a terminal rejection. `Escalate` is not a permit; it is a request for
an authority outside the current extractor lane to decide.

## Required Normalization

All extractors that observe equivalent source-level outcomes must map them to
the same graph decision:

| Source outcome | Canonical graph decision | Rationale |
| --- | --- | --- |
| `allow`, `permit` | `Permit` | The source policy grants the action. |
| `deny`, `block` | `Deny` | The source policy rejects the action. |
| `ask` | `Escalate` | The source policy asks another authority to decide. |
| `review` | `Escalate` | The source policy requires review before authorization. |
| `defer` | `Escalate` | The source policy defers authorization to another authority or time. |
| `escalate` | `Escalate` | The source policy explicitly escalates the decision. |

This normalization is lane-independent. A Python hook returning `ask`, a
TypeScript approval result of `Ask`, and a generic heuristic match on `"ask"`
must all produce `Decision::Escalate`.

## Conformance Rule

Per-extractor conformance tests must assert every supported lane's mapping for
`ask`, `review`, `defer`, and `escalate` when the source vocabulary includes
those outcomes. If a lane does not expose a given spelling, the test should
document the absence and still assert the lane's supported synonyms against the
canonical decision.
