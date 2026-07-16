# Extractor Boundary

The extractor claim is empirical/byte-stable at the Rust boundary and formal
only after bytes are represented as Lean artifacts.

## Formally Proved

- `BoundedExtractorContract` states the Lean-side source evidence, runtime
  kernel, and semantic bridge obligations for a modeled extractor.
- `bounded_extractor_contract_sound` proves that a contracted extractor maps a
  well-formed bounded source package to a semantic legitimacy kernel.
- `extractor_byte_stable_soundness_boundary` makes the boundary explicit: byte
  equality between a Rust run and Lean-modeled bytes is an external hypothesis,
  while Lean proves the contracted runtime and semantic obligations.
- `EmpiricalParityCertificate` formalizes the finite governance-admissibility audit fixture
  certificate once external byte-equality facts are supplied. AutoGen is the
  currently discharged leaderboard instance.
- `EmpiricalByteParityCertificate` and
  `canonical_leaderboard_fixtures_byte_parity_certificate` formalize byte
  parity for the full canonical leaderboard fixture set without claiming that
  every generated graph has a completed Lean governance-admissibility audit proof.

## Empirically Enforced

- `CanonicalInputs.lean` is the shared canonical fixture source of truth for
  Lean and Rust.
- Rust parity tests parse that shared Lean record list and check fixture source
  presence, deterministic source byte counts, deterministic source-tree hashes,
  repeated extraction byte stability, and byte equality with committed canonical
  graph snapshots.
- The routine verification gate runs the ordinary parity tests; the release gate
  additionally replays the slow leaderboard transcript snapshots and slow Codex
  extraction fixture.

## Not Verified

- Lean does not model or verify Rust operational semantics.
- Lean does not prove Rust parser or serializer correctness for arbitrary
  inputs.
- The canonical fixture certificate is finite. It is not a parser-correctness
  theorem for non-canonical inputs.
- Runtime-kernel claims for non-canonical or ill-formed inputs require their own
  evidence; they are not obtained from the canonical fixture parity certificate.
