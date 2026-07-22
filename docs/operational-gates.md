# Operational Gates

This page preserves operational verification material moved out of the root README. Return to the concise entry point at [README.md](../README.md), or use [boundary.md](boundary.md) for the formal/executable boundary.

## Reproducibility

Clone and enter the repository:

```bash
git clone https://github.com/abenenson/legitimacy
cd legitimacy
```

Run the canonical fast verification gate:

```bash
./scripts/verify.sh
```

`scripts/verify.sh` is the routine recommended check for a clean checkout. It checks formatting, clippy, the standard `cargo test` suite, Lean build, zero Lean `sorry`/`admit`/first-party `axiom`, spectral fixtures, public-surface documentation, doc alignment, legacy branding, and publication polish. Run `scripts/release-gate.sh` (or `scripts/verify.sh --release-gate`) at tag time to additionally replay slow transcript snapshots and extraction fixtures, delete first-party Lean oleans and rebuild from source via `scripts/verify-clean.sh`, check the README Lean-gate status line, the paper verification anchor, and stale package directories.

## Build Dependencies

The Lean build is reproducible from pinned public Lake dependencies. These
repositories are fetched by git URL during `lake build`; they are not vendored
into this repository.

| Lake dependency | Repository | License | Pinned revision | Load-bearing use |
| --- | --- | --- | --- | --- |
| `channel-capacity` | `https://github.com/abenenson/channel-capacity.git` | Apache-2.0 | `fdb4d1d18dba3e408fbe1969e09a4da3da2e313e` | Spine theorems `capability_scaling_shared_cliff` and `channel_capacity_bounds_C_star`. |
| `compact-spectral` | `https://github.com/abenenson/compact-spectral.git` | Apache-2.0 | `72cd62dbdd4c397d26fc0c5777d60fea2211e938` | Paper 04 compact spectral substrate. |
| `godel-loeb` | `https://github.com/abenenson/godel-loeb` | Apache-2.0 | `60a7a1098c34dbd0ee0833dde94ef5315f22d472` | Paper 03 reflective substrate. |

If you want to inspect each gate directly, run the component checks:

```bash
cd lean
lake exe cache get  # fetch prebuilt Mathlib artifacts (first build: hours -> minutes)
lake build
cd ..
cargo test
cargo clippy -- -D warnings
```


## CLI Surface

Build or install from source:

```bash
cargo build --release
cargo install --path .
```

Extract and audit a governance graph:

```bash
target/release/legitimacy extract tests/fixtures --emit-graph extracted.graph.json
target/release/legitimacy audit-graph --graph extracted.graph.json --claims tests/fixtures/sample_governance_claims.jsonl
target/release/legitimacy extract tests/fixtures --synthetic
target/release/legitimacy extract tests/fixtures --review-overlay tests/fixtures/sample_governance_review_overlay.json --claims tests/fixtures/sample_governance_runtime_claims.jsonl --claims-provenance observed-runtime
```

Compile and inspect policy artifacts:

```bash
legitimacy compile examples/claude-agent-sdk-permissions.rule[.]toml
legitimacy paradox examples/claude-agent-sdk-hooks.rule[.]toml
legitimacy certify examples/claude-agent-sdk-permissions.rule[.]toml --claimant Read --outcome 1
```

Run the protocol state machine over a graph policy artifact:

```bash
legitimacy protocol init examples/protocol-gate-graph.graph[.]toml > state.compiled.json
legitimacy protocol measure state.compiled.json > state.measured.json
legitimacy protocol activate state.measured.json > state.live.json
legitimacy protocol status state.live.json
legitimacy protocol audit state.live.json
```


## Gate Detail

`scripts/verify.sh` is the routine recommended check for a clean checkout. It checks formatting, clippy, the standard `cargo test` suite, Lean build, zero Lean `sorry`/`admit`/first-party `axiom`, spectral fixtures, public-surface documentation, doc alignment, legacy branding, and publication polish.

`scripts/release-gate.sh` and `scripts/verify.sh --release-gate` additionally replay slow transcript snapshots and extraction fixtures, run `scripts/verify-clean.sh` to remove `lean/.lake/build/lib/lean/Legitimacy*` and force a fresh `lake build`, check the README Lean-gate status line, the paper verification anchor, and stale package directories. GitHub Actions provides an optional, manually dispatched mirror; repository-local execution remains the canonical gate, and pushing a version tag does not spend Actions minutes automatically.
