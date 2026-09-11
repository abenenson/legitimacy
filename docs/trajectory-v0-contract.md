# Offline Single-Stream Trajectory Contract v0

## Status and scope

This document is normative for `legitimacy.trajectory.trace` version `0`.
`src/trajectory/` is the typed validation surface and
`schemas/trajectory-v0.schema.json` is its machine-readable JSON interchange
schema. V0 freezes validation and externally anchored deterministic replay; it
does not implement a source adapter, policy engine, or production authority.

The input model is one already-selected sequence of raw JSON records. Position
in that sequence is the only order. There is exactly one normalized event for
each raw record, and `sequence_index` and `raw_record.record_index` both equal
its zero-based position. A timestamp is ordinary source data and has no ordering
role. Separate stdout and stderr streams are not inputs to this model until an
adapter has an independently justified single source order; v0 does not merge
them.

`AgentActionEventV0` is a normalized occurrence and is neither
`ObservedRuntimeClaimRecord` nor `GovernanceClaim`. `event_id` identifies the
occurrence. `source_item_id` is optional and may recur across lifecycle
records. The historical observed-runtime importer and SQLite ledger chain have
no normative role here.

## Representation

A `TrajectoryTraceV0` contains:

- the exact schema binding;
- one run identity with a range citation or declared derivation binding;
- adapter and policy artifact bindings;
- a raw-capture record count and digest;
- a nonempty contiguous event sequence.

An artifact binding is the tuple `(identity, version, hash)`. Identity is 1–128
lowercase ASCII letters, digits, `.`, `_`, or `-`, begins with a letter or
digit, and version is 1–64 ASCII letters, digits, `.`, `_`, `+`, or `-`.
Digests are spelled exactly `sha256:` followed by 64 lowercase hexadecimal
digits. The schema binding is computed by
`trajectory_schema_binding_v0()` from the exact committed schema bytes.
Adapter, policy, capture-seal, and derivation bindings are compared with a
separately supplied `TrajectoryValidationContextV0`; a self-declared binding
is not self-authenticating.

The closed normalized event-kind vocabulary is:

- `action-request`
- `action-result`
- `observation`
- `message`
- `lifecycle`

The policy payload is a map from restricted artifact-name keys to individually
evidenced values. Values are tagged null, Boolean, canonical base-10 integer
strings, Unicode strings, arrays, or recursively keyed objects. Integer
spelling is `0`, a nonzero digit followed by digits, or `-` followed by a
nonzero digit and digits. `-0` and leading zeroes are invalid. Floating-point
values have no normalized representation in v0.

JSON interchange is UTF-8 RFC 8259 JSON. Before typed decoding, the Rust loader
rejects duplicate keys at every object depth, typed objects reject unknown
structural fields, and the enum rejects unknown kinds. The raw capture is
supplied to validation as an ordered vector of exact byte slices. Every slice
must decode as one JSON object under the same duplicate-key rule. Whitespace,
escape spelling, and any record-internal newline are retained only in those raw
bytes and therefore affect raw hashes. JSON decoding produces Unicode scalar
strings; canonical trace strings are their UTF-8 encoding with no Unicode
normalization. Platforms must not rewrite newlines or transcode raw records.
Occurrence and recurring source-item identifiers use the printable ASCII
profile `[A-Za-z0-9][A-Za-z0-9._:@/+-]{0,127}`; the exact value `unknown` is
reserved and invalid. Raw identifiers outside this profile require a named
deterministic adapter derivation that encodes or hashes them.

## Field-to-evidence contract

All normalized fields in the table are load-bearing. `cites-raw-range` names one
nonempty byte range in a sealed record and binds the exact bytes with a digest.
It does not assert that the normalized value occurs in, was decoded from, or is
semantically entailed by that range. `declared-derivation-binding` records an
allowlisted identity/version/hash and one or more unique source ranges. It does
not execute that artifact or check its claimed output. `unavailable` carries a
nonempty epistemic reason but fails validation wherever the table requires
evidence. Missing values, blank identity stand-ins, and the exact reserved
sentinel `unknown` do not satisfy the syntax.

| Field | Required evidence | Validation now |
|---|---|---|
| `run_id.value` | range citation or declared derivation binding | present, v0 printable ASCII identity profile, locator/binding valid |
| `events[*].event_id.value` | range citation or declared derivation binding | present, valid, unique in trace |
| `events[*].sequence_index.value` | range citation or declared derivation binding | present and exactly the zero-based raw-record position |
| `events[*].kind.value` | range citation or declared derivation binding | present and in the closed vocabulary |
| `events[*].source_item_id.value`, when present | range citation or declared derivation binding | present and valid; recurrence is allowed |
| `events[*].payload.*.value` | range citation or declared derivation binding | present, float-free, and recursively well formed |
| `events[*].raw_record` | whole-record reference, not field evidence | index equals source position and digest matches exact sealed record bytes |
| schema, adapter, policy | declared artifact binding | spelling valid; schema fixed; adapter and policy equal validation declarations |
| `raw_capture` | declared seal | count/digest equal validation declarations and recomputed exact record sequence |

## Canonical bytes

Canonical trace bytes are independent of JSON object order and JSON formatting.
No existing ledger or generic Serde encoding is canonical for this contract.

The primitive encodings are:

- `u64`: exactly eight bytes, unsigned, big-endian;
- byte/string frame: `u64(byte_length) || bytes`;
- string: a byte frame containing the exact UTF-8 scalar string, without
  normalization;
- Boolean: one byte, `00` false or `01` true;
- optional: one byte `00` for absent, or `01` followed by the value;
- sequence/map: `u64(element_count)` followed by encoded elements;
- map: entries sorted by key's raw UTF-8 bytes, each encoded as framed key then
  value.

`ValidatedTrajectoryTraceV0::canonical_bytes()` begins with the literal ASCII bytes
`legitimacy.trajectory.trace.canonical.v0` followed by `00`. It then encodes
these fields in order:

1. schema binding: identity, version, hash strings;
2. run ID: optional value then evidence;
3. adapter binding, then policy binding;
4. raw-capture record count, then digest string;
5. event count, then events in vector order.

Each event encodes in order: event ID; sequence index; kind; optional
source-item ID; raw-record index and digest; payload map. Event kinds are
encoded as their framed vocabulary strings.

Every evidenced field encodes the optional value before its evidence. Evidence
uses a one-byte discriminant: `00` cites-raw-range, `01` declared-derivation-binding, `02`
unavailable. Range-citation evidence then encodes its locator. Declared-derivation evidence encodes
the rule binding and its source-input sequence. Unavailable evidence encodes
its reason string. A locator encodes record index, byte offset, byte length,
and digest.

Normalized values use one-byte discriminants: `00` null, `01` Boolean, `02`
integer, `03` string, `04` array, `05` object. Boolean then encodes its one
byte; integer and string encode a framed string; array and object use the
sequence/map rules above.

## Hash preimages

Every v0 hash uses SHA-256 and the same envelope. For domain ASCII string `D`
and byte components `C₀,…,Cₙ₋₁`, the preimage is:

```text
"legitimacy.trajectory.hash.v0" || 00
|| u64_be(len(D)) || D
|| u64_be(n)
|| for i = 0,…,n-1: u64_be(len(Cᵢ)) || Cᵢ
```

The domains and components are:

| Hash | Domain `D` | Components |
|---|---|---|
| artifact binding | `legitimacy.trajectory.artifact.v0` | one component: exact artifact bytes |
| raw record | `legitimacy.trajectory.raw-record.v0` | one component: exact record bytes |
| source locator | `legitimacy.trajectory.source-locator.v0` | one component: exact located byte slice |
| raw capture | `legitimacy.trajectory.raw-capture.v0` | one component per record, in declared source order |
| canonical trace | `legitimacy.trajectory.trace.v0` | one component: validated `canonical_bytes()` |

The output spelling is `sha256:` plus the 32 digest bytes as lowercase
hexadecimal. The focused tests pin all five forms. In particular, the raw
capture's component count and each record length are in the preimage, so
concatenation ambiguity is impossible.

## Externally anchored replay

Replay format `legitimacy.trajectory.replay` version `0` is deterministic
integrity material constructed only from a `ValidatedTrajectoryTraceV0`. The
official serializer's private header and event helpers are the only canonical
field walk: whole-trace materialization joins the header and ordered event
bytes, while replay hashes those same per-event byte strings. Generic Serde is
not used to produce canonical trace or event bytes.

A replay candidate binds, in fixed JSON field order, replay format and version;
schema, adapter, and policy bindings; raw-capture count and digest; official
trajectory digest; replay record count; genesis head; ordered records; and
final head. Each record binds sequence index, event ID, raw-record digest,
canonical-event digest, previous head, and resulting head. Candidate JSON is
compact UTF-8 JSON followed by exactly one LF and is capped at 16 MiB. The
computed `final_head` is a report, not authority.

Replay hashes use the hash envelope defined above. All strings below are their
exact UTF-8 bytes, all counts and indices are eight-byte unsigned big-endian
integers, and each listed item is a separate framed component:

| Hash | Domain `D` | Ordered components |
|---|---|---|
| canonical event | `legitimacy.trajectory.replay.canonical-event.v0` | exact bytes returned by the shared canonical event encoder |
| genesis head | `legitimacy.trajectory.replay.genesis.v0` | replay format; replay version; schema identity, version, hash spelling; adapter identity, version, hash spelling; policy identity, version, hash spelling; raw-capture record count; raw-capture digest spelling; official trajectory digest spelling; replay record count |
| resulting record head | `legitimacy.trajectory.replay.chain-step.v0` | previous-head digest spelling; sequence index; event ID; raw-record digest spelling; canonical-event digest spelling |

Digest spellings are the already validated lowercase `sha256:` representation.
Framing the component count and every component length distinguishes, for
example, two-event identifier sequences `a`,`bc` and `ab`,`c` even though their
unframed concatenations are equal.

Replay authority uses Ed25519 receipts rather than promotable anchor JSON. A
`legitimacy.trajectory.replay-authority-receipt` version `0` contains issuer,
the exact algorithm label `ed25519`, key ID, nonzero authority epoch, a complete
`legitimacy.trajectory.replay-authority-anchor` version `0` tuple, and a
signature. The tuple binds replay format/version, schema, adapter, policy,
raw-capture seal, trajectory digest, record count, genesis, and expected final
head. There is no public replay-to-anchor constructor and no decoder that
turns receipt bytes into trusted authority.

Authority issuance consumes the exact trace, raw-record carrier, and validation
context. It validates those inputs and independently recomputes the replay and
complete anchor tuple before signing; it does not accept or read `replay.json`.
The Ed25519 message begins with the literal domain
`legitimacy.trajectory.replay-authority-receipt.signature.v0` plus `00`, then
length-frames the receipt format/version, issuer, algorithm, and key ID, encodes
the epoch as big-endian `u64`, and encodes every anchor field in its documented
order with strings length-framed and counts big-endian. This is the sole
authority signature serializer.

Verification separately decodes a
`legitimacy.trajectory.replay-authority-trust-policy` version `0` containing the
pinned issuer, `ed25519` algorithm, key ID, exact accepted authority epoch, and
Ed25519 verification key. Receipt and policy wires reject duplicate and unknown
fields. Only exact metadata and epoch equality plus strict Ed25519 verification
can mint `VerifiedReplayAuthorityReceiptV0`. Replay verification then
recomputes the complete replay from the validated trace, requires exact
candidate equality, and requires the authorized receipt's complete tuple to
equal the tuple derived from that recomputation. Only then can it mint
`legitimacy.trajectory.replay-verification` version `0` JSON.

The vendor-neutral CLI validation boundary uses three separate bounded inputs:
the closed trace JSON wire; a
`legitimacy.trajectory.exact-raw-record-set` version `0` JSON carrier whose
string values decode to the exact ordered raw-record bytes; and a
`legitimacy.trajectory.validation-declarations` version `0` object containing
the declared adapter, policy, raw-capture, and allowed-derivation bindings.
Neither decoding nor membership in `allowed_derivations` proves execution.
Both carrier objects reject duplicate and unknown fields. They feed
the existing trace decoder and validation routine rather than an alternate
validation path. The commands are:

- `canonicalize-trajectory-v0`, which publishes official canonical trace bytes;
- `build-trajectory-replay-candidate-v0`, which publishes an unverified replay candidate;
- `issue-trajectory-replay-authority-receipt-v0`, which independently consumes
  trace/raw/context plus an owner-private exact 32-byte Ed25519 authority key,
  recomputes the replay tuple, and publishes only the signed receipt; and
- `verify-trajectory-replay-v0`, which consumes the trace inputs, existing
  candidate, independently issued receipt, and separately configured trust
  policy before publishing verified success.

All inputs are read through bounded stable snapshots. The implementation-owned
snapshot vector and cap-plus-one staging allocation are explicitly zeroizing
and clear on every ordinary, error, and panic-unwind drop path; this statement
does not extend to compiler, syscall, or dependency temporaries outside the
implementation's control. Nonsecret inputs are validated before the fixed-size
owner-private authority key is opened. The authority input buffer is zeroized
immediately after construction of the signing key; the signing key is dropped
immediately after signing, before receipt serialization or publication, while
the zeroed stable snapshot remains held for input-identity revalidation. The
authority secret is absent from success artifacts and diagnostics. All outputs
use the same Linux no-replace, failure-atomic, owner-private publication
mechanism as the hardened trajectory adapter. Input, validation, verification,
collision, or pre-promotion write failure leaves no successful output path.
Diagnostics at this boundary are fixed closed codes and never use paths,
identifiers, or digest text as a semantic result.

The committed `tests/fixtures/trajectory-replay-v0/canonical-trace.bin` and
`replay.json` vectors have raw SHA-256 values
`245fb1d661b5a3a6831317407f04bfdf5b1f777adb28adcd9f6b27e51ed76850` and
`54ef8ec5d3a49eaa0d1eee0066696d363ccb0b945937c05f69d3d17a01b519f8`,
respectively. `reference.py` is a distinct Python standard-library
implementation of the canonical encoder and replay preimages; it must reproduce
both committed byte strings rather than invoking the Rust implementation.

The chain proves deterministic replay integrity and authority possession
relative to the separately configured pinned trust policy and its exact accepted
epoch. It does not prove source truth or completeness, pre-capture integrity,
trust-policy distribution, key custody, revocation, wall-clock freshness,
confidentiality or privacy, append-only storage, remote attestation, policy
correctness, per-step decision validity, temporal safety, enforcement,
causality, concurrency, leases, or liveness.

## Validation boundary

`TrajectoryTraceV0::from_json_slice` is the sole supported untrusted JSON
decoder. It enforces `MAX_TRACE_JSON_INPUT_BYTES_V0` against the exact supplied
wire, including insignificant whitespace, performs a complete duplicate-key
preflight, and then uses a private wire representation for closed-shape typed
decoding and integer-token enforcement. `TrajectoryTraceV0` intentionally does
not implement `Deserialize`; programmatic construction remains available, but
it is not an alternate untrusted-wire decoder.

`TrajectoryTraceV0::validate` first applies the cheap structural, cardinality,
and semantic resource budgets, then measures the exact deterministic compact
Serde encoding with a hard-capped counting writer. A typed trace whose official
compact form exceeds `MAX_TRACE_COMPACT_JSON_BYTES_V0` cannot yield a validated
token. This check occurs before raw-record JSON parsing and cryptographic
hashing. Validation then:

- checks schema, adapter, policy, and derivation binding syntax and declared
  equality;
- compares the trace's declared capture seal with the separate validation declarations;
- recomputes capture, whole-record, and evidence-range digests;
- memoizes each exact cited range so it is charged and hashed once per
  validation call;
- checks one event per raw record, nonempty cardinality, contiguous
  source-position indices, and unique event occurrences;
- rejects missing/unavailable load-bearing values, undeclared or input-free
  derivations, malformed locators, malformed integers, and invalid IDs.

Successful validation returns a borrowing `ValidatedTrajectoryTraceV0` token.
Only that token exposes the official bounded compact JSON export through
`to_compact_json()`, using the same hard-capped serializer path as validation,
as well as the canonical-byte and trajectory-digest surface. Generic
`Serialize`, including arbitrary pretty or custom serialization, is not the
official bounded interchange format.

V0 has mandatory finite limits: 8 MiB exact untrusted trace JSON input and
8 MiB official deterministic compact JSON export; 64 MiB raw capture; 8 MiB
per raw record; 10,000 raw records and events; 256 fields per payload or nested
object; 50,000 payload fields, 8 MiB normalized content/key bytes, and 100,000
normalized nodes total; depth 32; 1,024 items per array or derivation; 100,000
evidence locators; and 16 MiB summed across distinct cited ranges. Identifiers
are at most 128 bytes,
normalized integers at most 1,024 digits, normalized strings at most 16,384
Unicode scalars and 65,536 UTF-8 bytes, and unavailable reasons at most 1,024
bytes. Duplicate-key preflight accepts at most 1,024 keys and 65,536 cumulative
decoded UTF-8 key bytes in each trace or raw-record JSON object. All limits are
conjunctive upper bounds, so saturating one budget does not promise that
another, especially compact JSON, remains below its cap. All accumulated sizes
use checked arithmetic, and cheap size/cardinality checks precede raw JSON
parsing and contract hashing.

The JSON Schema is a structural pre-screen: its numeric ceilings mirror the v0
operational resource limits and are exactly representable by IEEE-754
validators. JSON Schema models mathematical integers and may therefore accept
lexical forms such as `1.0` and `1e0`, while Rust requires integer tokens.
Runtime validation remains authoritative for contextual equality and range
checks against the actual capture. The committed schema is LF-pinned by
`.gitattributes`, and its exact LF bytes remain hash-bound.

Mutation and tail truncation are detected relative to the separately supplied
capture digest and record count. Replacing raw bytes, trace, and validation
declarations together can pass validation; replay authority blocks verified
success unless the configured authority independently signs that replacement.

The generic validator proves only that cited ranges exist and match their
digests. It does not interpret vendor JSON, prove that a normalized value is
represented by the cited bytes, execute a declared derivation, or compare a
derivation output with the normalized value. This semantic-binding gap remains
an adapter-specific conformance obligation; replay-authority verification
neither closes it nor introduces a generic decoder. Adapter conformance must
define the concrete
source contract, preserve required source kinds without silent dropping,
demonstrate value-to-evidence entailment, execute registered derivations, and
must not synthesize `unknown`, empty, zero, or other manufactured identity
stand-ins. Policy execution, per-step decision validity, and temporal
composition are not claims of this integrity-only replay contract. The narrow
normalized-event extension is documented separately in
[`trajectory-composition-v0.md`](trajectory-composition-v0.md).

## Normative threat/claim matrix

| Surface | V0 claim |
|---|---|
| Single-stream order | Exact source-record position is validated; timestamps do not affect it. |
| Structural ambiguity | Duplicate JSON keys, unknown structural fields/kinds, float-bearing normalized payloads, malformed bindings, and malformed evidence fail closed. |
| Referential integrity | Exact raw records and cited ranges are recomputed against separate declarations; this is byte-range citation, not semantic observation. |
| Replay authority | Verified success requires a receipt signed by the key pinned in the separate trust policy at the exact accepted epoch. |
| Explicit nonclaims | Value-to-range semantic entailment; derivation execution/output; source truth or completeness; pre-capture integrity; trust-policy distribution; key custody/revocation; confidentiality or privacy; append-only storage; remote attestation; policy correctness; per-step decision validity; temporal safety; enforcement; causality or concurrency; leases; liveness. |

Distributed-order and semantic-binding extensions require a later triggered
version rather than speculative placeholders in this contract.
