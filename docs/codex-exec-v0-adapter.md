# Codex `exec --json` v0 adapter

## Status and source pin

Only the exact statements in the marked contract regions are normative; all remaining text is explanatory and cannot amend or override them.

This document describes `legitimacy.codex-exec-v0.adapter` version `0`. The
adapter accepts a deliberately narrow, single-turn language emitted by Codex
CLI package version `0.144.0`.
The authoritative source is the annotated tag `rust-v0.144.0`, tag-object
`e0a9ff6938d85db1a7b11a693b6aa2bc31fe5a55`, peeled commit
`767822446c7a594caa19609ca435281a9ec67e0d`. The tracked source manifest
records the exact SHA-256 of every inspected Rust source from that peeled
commit. Its ordered source set is:

- `codex-rs/exec/src/exec_events.rs`: `ThreadEvent`, event structs,
  `ThreadItemDetails`, item structs, usage, lifecycle status, and patch-kind
  wire types;
- `codex-rs/exec/src/event_processor_with_jsonl_output.rs`:
  `EventProcessorWithJsonOutput`, `emit`, `next_item_id`,
  `map_item_with_id`, lifecycle ID reconciliation, warning/error projection,
  todo reconciliation, active-item completion ordering, usage defaulting, and
  turn terminal projection;
- `codex-rs/exec/src/cli.rs` and `codex-rs/cli/src/main.rs`: the Clap
  fresh-exec/resume/review split, global exec arguments, and resolved fresh
  invocation;
- `codex-rs/protocol/src/thread_id.rs`: the `ThreadId` UUID wrapper,
  `Uuid::now_v7()` construction, parsing, and canonical display;
- `codex-rs/app-server-protocol/src/protocol/item_builders.rs` and
  `codex-rs/app-server-protocol/src/protocol/v2/item.rs`: item construction,
  file-change ordering, and public item wire projection;
- `codex-rs/exec/src/lib.rs` and `codex-rs/cli/src/exit_status.rs`: exec
  termination and process exit behavior.

The TypeScript SDK and the historical
`src/extract/codex_observed_runtime.rs` importer are not authorities. The
legacy importer is never invoked by this adapter.

The committed fixtures are synthetic shapes derived from those Rust
definitions. Their receipt class is `synthetic-fixture`; they make no claim
about an executable, process, sandbox, stdin, stderr, termination, or actual
Codex observation.

## Exact attachment framing and budgets

The attachment is exact stdout only. Stderr is separately sealed by a genuine
process receipt and is never merged into JSONL. Every record must be one UTF-8
JSON object followed by LF. The final LF is mandatory. Empty input, blank
lines, CR/CRLF, a missing final LF, non-object roots, malformed UTF-8, trailing
material, and record-internal literal LF framing fail before mapping.

The CLI reads a filesystem input once through a `cap + 1` bounded buffer.
Metadata length is advisory. After its inode and preflight checks it moves that
owned buffer into `adapt_codex_exec_owned_v0`; a successful adapted value owns
that one full raw attachment plus compact ranges and metadata. The slice API is
a convenience that necessarily makes one owned copy. Framing scans the bounded
buffer into record ranges without `read_line` or `lines().collect()`, and
retains those ranges for revalidation. Sensitive adapted and framing types are
not `Clone`. Limits are inclusive:

| Resource | Limit |
|---|---:|
| complete JSONL | 8 MiB |
| one record | 512 KiB |
| records/events | 4,096 |
| JSON nesting depth | 16 |
| nodes per record | 32,768 |
| decoded keys per record | 8,192 |
| decoded string/key bytes per record | 384 KiB |
| private authority receipt | 2 MiB |
| trusted adaptation context | 64 KiB |
| serialized adapter bundle | 16 MiB |
| argv arguments / one argument / aggregate | 32 / 4 KiB / 32 KiB |
| workspace manifest entries | 256 |
| held native executable | 384 MiB |
| held release archive | 256 MiB |
| held Sigstore bundle | 4 MiB |
| held capture profile | exact embedded profile length |
| held private stdin | 1 MiB |
| running capture-tool image | 512 MiB |

Each held process input is rejected from descriptor metadata before hashing
when its role limit is exceeded. Whole-file hashing independently stops at
that same role limit plus one byte, and reopen verification repeats both the
metadata and bounded-content checks.

`src/trajectory/duplicate_json.rs` supplies the one duplicate-aware streaming
scanner. The adapter applies its own named depth/node/key/string limits, then
collapses every scanner or Serde detail into a closed diagnostic. It never
prints an attacker-controlled field name, value, parser message, or path.

## Closed wire language

Objects have exactly the following properties. Every nested object is closed.
Usage has exactly `input_tokens`, `cached_input_tokens`, `output_tokens`, and
`reasoning_output_tokens`, each a nonnegative integer token.

| Record | Accepted shape |
|---|---|
| `thread.started` | `{type,thread_id}` |
| `turn.started` | `{type}` |
| `turn.completed` | `{type,usage}` |
| `turn.failed` | `{type,error:{message}}` |
| `error` | `{type,message}`; nonterminal |
| completed `agent_message` | item `{id,type,text}` |
| completed `reasoning` | item `{id,type,text}`; whitespace-only is rejected because the emitter omits it |
| completed item `error` | item `{id,type,message}` |
| started `command_execution` | item `{id,type,command,aggregated_output,exit_code,status}` with `in_progress`, empty output, and null exit |
| completed `command_execution` | the same properties with `completed`, `failed`, or `declined` |
| started `file_change` | item `{id,type,changes,status}` with `in_progress` |
| completed `file_change` | the same properties with `completed` or `failed` |
| started/updated/completed `todo_list` | item `{id,type,items:[{text,completed}]}` with no invented status |

File changes are strictly path-sorted and contain exactly `{path,kind}`, where
kind is `add`, `delete`, or `update`. `mcp_tool_call`, `collab_tool_call`,
`web_search`, every unknown record/item/status/property, and every other
lifecycle combination fail with no trace. Although the source processor can
allocate a fresh completion ID for an item whose start was not visible, this
profile rejects orphan command and file completions. That is a narrower
complete-lifecycle language, not a statement that other Codex streams are
malformed.

The exact fresh-turn FSM requires:

1. one `thread.started` as record zero;
2. one `turn.started`;
3. only top-level `error` or completed item `error` diagnostics before the
   turn;
4. canonical first occurrences `item_0`, `item_1`, and so on;
5. recurrence only for the same active command or file change, and at most one
   allocated todo list in the turn;
6. every todo update reuses that one ID and replaces the stored latest item
   vector; todo completion must reproduce that exact latest vector;
7. todo completion at terminal notification precedes reconciliation of
   unfinished commands/files; after it, only completions of already-active
   commands/files may occur before the visible terminal—no start, todo update,
   message, diagnostic, or other event may interleave;
8. legal status transitions, with no active item at the visible terminal;
9. exactly one `turn.completed` or `turn.failed`, followed by EOF.

Todo completion is legal before either visible terminal kind. Interrupted
execution remains outside the accepted no-terminal profile. Multiple-turn
streams are rejected. Outside the post-todo reconciliation interval,
top-level errors may appear on either side of `turn.started` and remain
nonterminal.

## Observable projection

Every accepted record becomes exactly one `AgentActionEventV0`. Source position
is both `sequence_index` and `raw_record.record_index`. Whole-record bytes are
the bounded source locator for decoded and enum-derived fields. The mapping is:

| Source projection | Normalized kind |
|---|---|
| thread/turn lifecycle and todo lifecycle | `lifecycle` |
| command/file start | `action-request` |
| command/file completion | `action-result` |
| agent message and public reasoning summary | `message` |
| top-level and item error projection | `observation` |

Under this exact fresh-exec profile, `thread_id` is accepted only as canonical
lowercase UUIDv7 text: exactly 36 ASCII bytes, hyphens at byte offsets 8, 13,
18, and 23, lowercase hexadecimal elsewhere, `7` at offset 14, and RFC variant
`8`, `9`, `a`, or `b` at offset 19. No other UUID spelling or arbitrary thread
string reaches mapping.

Payloads retain only closed structural labels, the observed canonical thread
ID, nonnegative usage integers, command exit-code projection, file change
kinds and count, and todo completion Booleans. Model prose, reasoning text,
error text, commands, aggregated command output, patch paths, and todo text are
not normalized. `source_item_id` preserves the exec-stream `item_N`, not an
upstream vendor ID.

The adapter does not strengthen lossy observations. Zero usage is labeled
`emitter-total-or-zero-default`; empty aggregated output is not called observed
empty; file status `failed` is labeled `failed-or-declined-projection`;
top-level error is not called fatal; item error is not process failure; and no
policy result is inferred.

The first observed thread ID is not itself the normalized run identity. The run
ID is a domain-separated derivation over the exact `thread.started`
whole-record digest and decoded canonical thread ID. Its evidence declares the
full record-zero locator. Each event ID is a domain-separated derivation over
that run ID, the big-endian source position, and that event's whole-record
digest. Event-ID evidence declares the primitive locators needed to recompute
it: record zero and the current record, deduplicated for event zero. Field and
position derivations retain their exact record-level sources. The trace-level
raw-capture seal independently binds the entire attachment. No identifier uses
a timestamp, clock, host state, random value, model prose, or optional vendor
item ID. Every derivation has a named artifact binding and is regenerated by
serialized bundle revalidation.

The process profile accepts exactly the lowercase-hex argv bytes for this
ordered grammar:

```text
codex exec --json --ephemeral --ignore-user-config --ignore-rules
--skip-git-repo-check --sandbox read-only -
```

The prompt is forced through sealed stdin. Resume, review, positional prompts,
opaque config overrides, alternate ordering, and all other resolved modes are
unsupported. Bytes are decoded from lowercase hex and never treated as UTF-8
for grammar matching.

For genuine process authority, terminal relations are:

| Visible terminal | Accepted process termination |
|---|---|
| `turn.completed` | `exited(0)` or `exited(1)` |
| `turn.failed` | `exited(1)` |

Exit codes are bounded to `0..=125`; signals are represented separately as
`signaled(signal,core_dumped)` with signals `1..=64`. This strict profile
rejects all signaled receipts as unsupported and never performs a shell-style
`128 + signal` collapse.

## Authority receipts and commitments

<!-- codex-exec-v0-contract:bindings:begin -->
Binding contract: `legitimacy.codex-exec-v0.adapter` uses domain
`legitimacy.codex-exec-v0.adapter-source-manifest.v0` and scopes
`adapter-core`; `legitimacy.codex-exec-v0.sanitizer` uses domain
`legitimacy.codex-exec-v0.sanitizer-registered-source-manifest.v0` and scopes
`adapter-core`, `sanitizer`; `legitimacy.codex-exec-v0.cli-publication` uses
domain
`legitimacy.codex-exec-v0.cli-publication-registered-source-manifest.v0` and
scopes `selected-cargo-build`, `normative-contract`; and
`legitimacy.codex-exec-v0.fixture-spec` uses domain
`legitimacy.codex-exec-v0.fixture-source-manifest.v0` and scopes
`fixture-spec`.
Sanitizer registry contract: the complete ordered `sanitizer` registry contains
`sanitizer.rs`, `sanitizer_jwt.rs`, `publication_authority.rs`, `lineage_sidecar.rs`.
<!-- codex-exec-v0-contract:bindings:end -->
<!-- codex-exec-v0-contract:entropy:begin -->
Entropy contract: on Linux, a production nonce is 32 bytes filled by
`rustix::rand::getrandom` with `empty` flags; the fill policy is
`retry-interrupted-accept-bounded-partial`, and the rejection policy is
`unsupported-platform-zero-oversized-failed-all-zero`.
<!-- codex-exec-v0-contract:entropy:end -->
<!-- codex-exec-v0-contract:process-failure-precedence:begin -->
Process failure contract: after complete cleanup, primary precedence is
`capture-stdout-overflow`, `capture-stderr-overflow`, `capture-stdin`,
`stream-state`, `capture-timeout`, `capture-live-descendant`.
`capture-live-descendant` means `known-main-status-with-fresh-live-owned-descendant`;
`capture-cleanup` dominates for `cleanup-operation-error`,
`worker-join-uncertainty`, `final-absence-unproven`. Success requires
`fresh-process-tree-absence`, `all-workers-complete`.
<!-- codex-exec-v0-contract:process-failure-precedence:end -->

`InputAuthorityReceiptV0` is a closed sum:

- `SyntheticFixtureReceiptV0` binds the emitter identity, exact full JSONL
  length/digest, raw record count/seal, source-derived fixture manifest, and
  nonce. It contains no process fields.
- `ProcessCaptureReceiptV0` binds the pinned emitter, executable file digest
  and `(dev,ino)`, bounded byte argv, resolved mode/profile, explicit
  stdin presence and seal, discriminated termination, separate stdout/stderr
  seals, record count/capture seal, executed capture-tool binding/digest/inode,
  capture-profile artifact, allowlisted workspace members/tree digest, release
  asset, Sigstore bundle, verification status, and nonce.
- `SanitizedDerivedCaptureReceiptV0` binds only lineage and bytes that the
  sanitizer produced: origin class, hiding parent commitment, private parent
  full-JSONL facts/seal, sanitizer policy/artifact, derived full-JSONL
  facts/seal, and nonce. It contains no executable, argv, stdin, stderr,
  termination, or process claim for derived bytes.

The shareable sanitized bundle is also a closed public revalidation boundary.
Given the exact sanitized child, it checks the public derived projection,
schema/adapter/sanitizer/policy bindings, child length and seals, then reruns
framing, parse, FSM, mapping, trace validation, canonical serialization, and
payload-manifest construction. Exact comparison against every deterministic
public bundle component is required. This establishes only the public derived
authority and exact child; it does not establish the hidden parent link. That
separate claim requires the owner-private lineage sidecar.

On Linux, the owner-private `legitimacy-codex-capture-v0` binary is the sole
production constructor for `ProcessCaptureReceiptV0`. It requires explicit
paths for the pinned native ELF, release archive, present-but-unverified
Sigstore bundle, structured-stdin artifact, empty workspace, exact capture
profile artifact, and a new output directory. It executes the held ELF through
`fexecve`, captures bounded streams and exact termination, and publishes
`stdin.bin`, `stdout.jsonl`, `stderr.bin`, and
`process-capture-receipt.json` with owner-only no-clobber semantics. The
producer source binding uses identity
`legitimacy.codex-exec-v0.capture-producer`, domain
`legitimacy.codex-exec-v0.capture-producer-source-manifest.v0`, and scope
`capture-producer`. This producer does not verify the Sigstore signature and
does not claim filesystem confinement beyond the fixed Codex sandbox profile
and held read-only-during-exec workspace discipline.

The capture process inherits the implementation's allowlisted environment,
including service endpoint, proxy, and TLS inputs; the receipt binds the
resulting bytes but does not establish remote service or model identity.

The public library transaction enforces the same single-purpose process
boundary as the binary before changing the process-global child-subreaper
state: the host must have exactly one live thread and no preexisting child.
The transaction blocks `SIGCHLD`, installs its default disposition, and becomes
a child subreaper before spawning workers. Before exec, the child opens its own
pidfd and race-freely transfers it over a close-on-exec Unix socket. The child
waits for an acknowledgment before restoring the caller's signal state and
executing the held ELF; the parent acknowledges only after its dedicated receipt
worker owns the transferred pidfd. Receipt retries only an interrupted `recvmsg`.
Every other receive error, a truncated control message, or a consumed handle-less
packet closes the channel without acknowledgment, so the pre-exec hook fails and
`Command::spawn` reaps the child before returning an error. A malformed packet
that installed a descriptor retains that handle until spawn failure is observed.
Thus every successful spawn already has identity-stable signal authority and no
fallible post-spawn fallback acquisition exists. Later adopted
children are discovered only as current direct children and converted to
pidfds while they cannot be reaped or PID-recycled. All TERM and KILL delivery
uses those pidfds; numeric PID and process-group signaling are forbidden.
Nonblocking main-child waits, pidfd-relative adopted-child reaping, and fresh
direct-child observations accumulate cleanup uncertainty until every owned
pidfd is reaped and a new observation proves the direct-child set empty.
Historical uncertainty remains sticky for the verdict, but a later successful
observation/reap cycle may complete the absence proof and immediately ends
signaling. A live owned set without that proof progresses through the bounded
TERM and KILL phases. Every created pipe worker is nonblocking, cancellable,
and joined before signal state, subreaper state, and workspace restoration. A
cleanup operation error or unproven absence fails closed as `capture-cleanup`;
`/proc` failure is never child-absence evidence.

The executed capture-tool digest and inode are read from one held
`/proc/self/exe` descriptor and that descriptor remains held through receipt
construction. They identify the producer file executing this transaction even
if its ordinary pathname is moved or replaced. This is executed-file identity,
not remote attestation or reproducible-build proof.

Every private receipt contains a 32-byte nonce encoded as 64 lowercase hex
digits. Its serialized nonce-source label is an asserted input property, not
proof of how imported bytes were generated. On Linux, each local production
draw is filled by `rustix::rand::getrandom` with empty flags. The fill loop
retries interruptions, accepts bounded partial reads, and rejects zero-length,
oversized, failed, or all-zero results. Other platforms fail as unsupported.
The production publication transition makes separate draws for the sanitized
derived-capture nonce and publication-parent reblinding nonce, rejects equal
material, and creates its nonserializable mint only after both draws succeed.
The two calls and equality check establish separate route invocations and
distinct role material under the honest-kernel boundary, not statistical
independence against a hostile kernel.
Deterministic tests supply explicit fixed material for both roles through a
distinct result type that has no publication transition. The private authority
commitment is SHA-256 under
`legitimacy.codex-exec-v0.authority-commitment.v0` over an explicit,
versioned, length-framed canonical field encoding that includes the nonce.
Generic Serde output and JSON object order are not canonical. The receipt does
not hash itself. Guessable prompt/stdin fields have no public unblinded
projection.

Adapter domain hashes reuse the length-framed SHA-256 envelope defined by the
trajectory v0 contract. Their complete scopes are:

| Digest | Domain and ordered components |
|---|---|
| synthetic/derived full JSONL | `legitimacy.codex-exec-v0.full-jsonl.v0`; one component containing every JSONL byte, including every separator and final LF |
| authority commitment | `legitimacy.codex-exec-v0.authority-commitment.v0`; one component containing canonical receipt bytes |
| run ID | `legitimacy.codex-exec-v0.run-id.v0`; record-zero whole-record digest spelling, then decoded canonical thread-ID bytes |
| event ID | `legitimacy.codex-exec-v0.event-id.v0`; normalized run-ID bytes, `u64_be` source position, then whole-record digest spelling |
| payload component | `legitimacy.codex-exec-v0.payload-component.<role>.v0`; one component containing the exact component bytes |
| workspace tree | `legitimacy.codex-exec-v0.workspace-tree.v0`; for each member in order: `u64_be` ordinal, role bytes, format bytes, lowercase-hex relative-path bytes, `u64_be` length, SHA-256 spelling, `u64_be` device, and `u64_be` inode |

Source-derived artifact bindings use the same framed SHA-256 envelope. Their
identities, framing domains, and named registered scopes come from the
implementation-owned `CODEX_EXEC_*_BINDING_CONTRACT_V0` constants.

- The adapter identity is `legitimacy.codex-exec-v0.adapter`, its domain is
  `legitimacy.codex-exec-v0.adapter-source-manifest.v0`, and its
  `adapter-core` scope covers the ordered duplicate-aware scanner and adapter
  modules defining parsing, FSM, mapping, receipts, bundles, wire forms,
  validation, errors, framing, and public construction.
- The sanitizer identity is `legitimacy.codex-exec-v0.sanitizer`, its domain
  is
  `legitimacy.codex-exec-v0.sanitizer-registered-source-manifest.v0`, and its
  ordered scope is the complete `adapter-core` registry followed by the
  complete ordered `sanitizer` registry declared in the binding contract
  above.
- The CLI publication identity is
  `legitimacy.codex-exec-v0.cli-publication`, its domain is
  `legitimacy.codex-exec-v0.cli-publication-registered-source-manifest.v0`,
  and its embedded component is the canonical selected-build object. That
  object classifies the selected executable and library inputs, binds the
  complete `Cargo.lock`, manifest, build script, provenance inputs, and this
  contract document, and records absent repository Cargo/toolchain
  configuration roots.
- The fixture-spec identity is `legitimacy.codex-exec-v0.fixture-spec`; its
  domain is `legitimacy.codex-exec-v0.fixture-source-manifest.v0`, and its
  `fixture-spec` scope is the exact tracked source-manifest path and bytes.

The adapter, sanitizer, and fixture registries alternate an explicit
repository-relative path and exact `include_bytes!` bytes in order. The CLI
publication binding instead embeds only the canonical selected-build object;
rustc dep-info for the selected binary and linked library independently
reconciles its compiler-input roles. The sanitizer policy remains a distinct
policy artifact binding over policy bytes; it is not the sanitizer
implementation binding.

These are source-byte review receipts: a changed listed path, listed source
byte, or tracked upstream manifest byte changes its advertised binding. The
contract document is included as review evidence, while structural tests
separately reconcile its security declarations to implementation. The
selected-build object records bytes observed by this verifier for dependency
paths reported by one selected repository build. Each selected compiler and
bound noncompiler input is descriptor-walked from the canonical repository
directory: every symlink is rejected, the final object must be a regular file
strictly below that root, the opened descriptor supplies the hashed bytes, and
metadata plus component identities are revalidated. Under the stated
honest-concurrency boundary this does not prove which bytes a hostile or
concurrently raced compiler read.

The selected-build receipt does not bind toolchain binaries, global Cargo
configuration, the ambient environment, host/target/profile/flags/linker, the
operating system, dependency source bytes beyond the stated lock/build
closure, or distributed executable bytes. The CLI publication binding is
locally reportable and is not carried in the adapter bundle. Output paths
resolve to pinned directory objects under the same honest-concurrency
nonclaim. No binding hashes a serialized bundle that contains the binding.

Canonical receipt bytes start with
`legitimacy.codex-exec-v0.authority.canonical.v0` plus NUL. The authority
variant and every field name/value then appear in fixed source order. Strings
are `u64_be(byte_length) || UTF-8 bytes`, integers are `u64_be`, lists start
with their `u64_be` count, Booleans/discriminants are one byte, and bindings,
seals, inodes, and manifest members expand into explicitly ordered primitive
fields. Every private field, including the nonce, is encoded; no commitment or
receipt field is omitted.

Executable, stdin, stdout, stderr, capture-tool file, workspace tree/member,
release-asset, and Sigstore `sha256:` fields are ordinary SHA-256 over the
exact attested file or stream bytes. Artifact-binding hashes use
`artifact_digest_v0`. Raw record/capture/locator and canonical trajectory
digests retain their separately documented trajectory-v0 domains.

The caller-trusted context supplies the expected hiding authority commitment
and downstream governance-policy context binding. Both are out-of-band. The
schema binding comes from `trajectory_schema_binding_v0()` and the adapter
binding from its embedded reviewed source manifest. Capture and sanitizer
bindings never substitute for `trace.policy`; the adapter binds that field but
does not parse, execute, or judge the downstream policy.

Raw-verifiable stdout length/digest/count/seal are recomputed. Stdin, stderr,
manifest, executable, capture-tool, release, Sigstore, and termination facts
are typed trusted attestations relative to the caller-supplied commitment; the
adapter cannot re-observe them.

The strict process shape additionally fixes
`executable_execution_binding=fexecve-held-fd`,
`artifact_open_discipline=held-fd-no-symlink`, and
`workspace_execution_discipline=held-read-only-during-exec`. Workspace
members have contiguous zero-based ordinals, strict increasing lowercase-hex
relative paths, role `fixture-input`, format `regular-file-bytes`, and exact
length, SHA-256, device, and inode fields. Validation recomputes the canonical
workspace-tree digest above and compares it to the receipt. The one official
Linux x64 process profile also requires the executed executable SHA-256 to
equal its pinned release member digest. These checks establish receipt
self-consistency relative to the trusted commitment; they do not re-observe
the workspace or recreate the capture operation.

## Transformation receipts and bundles

`TransformationReceiptV0` is separate from input authority. Its private form
binds authority commitment, exact authorized capture seal, adapter, schema,
downstream context, transformation policy, normalized trace digest, optional
derived seal, and an ordered payload manifest.

The manifest excludes the transformation receipt and bundle envelope. It has
exactly these ordered roles:

1. `official-trace-json`, format `trajectory-v0-compact-json`;
2. `canonical-trace`, format `trajectory-v0-canonical-bytes`.

Each entry fixes role, format, ordinal, byte length, and a role-specific
domain-separated digest. There is no recursive whole-bundle hash.

`PrivateAdapterBundleV0` is owner-only and includes the private transformation
receipt. The sealed publication owner derives a private lineage commitment
under `legitimacy.codex-exec-v0.owner-private-lineage-commitment.v0`. Its
framed input binds the original parent commitment, fresh local reblinding
nonce, asserted input evidence declarations, downstream policy, adapter,
schema, sanitizer policy, and sanitizer implementation. That commitment and
its preimage material exist only in the owner-private sidecar.
`ShareableSanitizedBundleV0` contains the child length, seal, trace,
payload manifest, and exact compiled schema/adapter/sanitizer/policy bindings.
It has no parent evidence class, parent receipt, parent commitment, derived
private-receipt commitment, reblinding nonce, parent raw seal, parent trace,
parent record/locator digest, parent nonce, sidecar bytes, or private manifest.
Its public evidence class is `sanitizer-conforming-child-projection`: untrusted
verification proves the exact child, its conformance to the public privacy
validator, and deterministic compiled projections. It does not prove that the
compiled sanitizer produced that child. Preserving the stronger
`sanitized-derived-capture` class would require a publication-authority receipt
rooted in a trust policy supplied independently from the bundle; this interface
does not accept such a policy. The owner-private sidecar separately proves the
exact hidden parent-child lineage and is not a public minting route.

Public semantic receipt and bundle fields are private and their API is
Serialize-only. Untrusted loading produces distinct inspect-only types.
Revalidation requires the exact attachment, private authority receipt, and
complete trusted context. It:

1. recovers the explicit official trace component and calls
   `TrajectoryTraceV0::from_json_slice`;
2. validates that supplied trace against the exact raw attachment;
3. reruns framing, strict parsing, FSM, complete mapping, and trajectory
   validation to obtain a fresh borrowing token;
4. regenerates compact JSON, canonical bytes/digest, manifest, receipts, and
   the correctly typed bundle;
5. compares the deterministic serialized bundle byte-for-byte.

Consequently, mutating a derived run/event ID, kind, status, payload, evidence,
or locator and recomputing bundle-local hashes still fails regeneration. No
serializable validation Boolean, unchecked trace decoder, unsafe lifetime, or
self-referential owner/token is used.

## Sanitizer and CLI

`sanitize_capture_v0` validates the exact synthetic or genuine parent, then
uses per-slot encounter-order placeholders. Equality is retained only within
the declared thread, message, reasoning, diagnostic, command, output, path, or
todo-text slot. Structural types, lifecycle, canonical `item_N`, closed
statuses, integers, and Booleans remain. All free text, command output, paths,
and identity-like source strings are replaced.

<!-- codex-exec-v0-contract:sanitized-identity:begin -->
Sanitized identity contract: domain
`legitimacy.codex-exec-v0.sanitized-thread-id.v0` hashes
`asserted-nonce-source-label`, `nonce-bytes-32` and projects the digest as
`uuid-version-7`, `rfc-variant`, `canonical-lowercase`.
<!-- codex-exec-v0-contract:sanitized-identity:end -->

The deterministic sanitized thread identity is derived under
`legitimacy.codex-exec-v0.sanitized-thread-id.v0` from the asserted nonce-source
label and all 32 nonce bytes. The first 16 digest bytes are then forced to the
UUIDv7 version and RFC variant bits and rendered as canonical lowercase text.
Thus identical nonce-source labels and bytes repeat the child identity, while
different nonce material is not collapsed to a constant placeholder. A
trailing JSON whitespace byte before each record LF keeps every derived record
locator/digest distinct from its parent without changing decoded structure.

The sanitizer structurally scans the child, creates the correctly typed
derived receipt and trusted context, then reruns exact framing, closed parsing,
FSM, mapping, and trajectory validation over the exact derived bytes. The
production entry returns a transaction with read-only sanitized JSON access
and one consuming `into_publication_pair(self)` transition. Its private mint
and the authoritative bundle storage exist only in the singleton
`publication_authority.rs` owner. Rust ownership permits one authoritative
bundle construction per transaction; copying already serialized bytes or
serializing the constructed bundle again is not a new authority transition.
The owner-private sidecar retains the original parent commitment, private
lineage commitment, and reblinding nonce for exact private-pair validation.
Import revalidation invokes
the same private renderer only for comparison bytes and returns an inspect-only
validation handle, never a mint, transaction, or authoritative bundle.

A bounded typed privacy validator covers generated and imported child JSONL and
the final shareable bundle/trace/projection surface. Only the `thread_id` slot
of a `thread.started` child record, and its exact derived trace value, may carry
the generated UUIDv7. Other UUID variants and UUIDv7 values in other slots,
dotless account/email forms, bounded access-key and JWT shapes, IPv4/IPv6,
bounded scheme forms, root and Windows home paths, Unicode whitespace, and
non-text bytes in text surfaces are rejected. Access-key tokens are either at
least 11 ASCII token bytes beginning `sk-` or `sk_`, or exact 20-byte uppercase
`AKIA`/`ASIA` forms. JWT-like tokens have exactly three nonempty base64url
segments, total length at least 12, segment length at least two, and no segment
with an impossible base64url length modulo four. The first two segments must
use canonical unpadded base64url and decode as JSON objects. If either encoded
header or payload exceeds 4,096 bytes, the lexically qualifying token is
rejected without decoding that segment. Scheme
recognition covers the
2-to-16-byte ASCII scheme grammar followed by `://`, plus case-insensitive
`data:` and `javascript:` forms; typed `sha256:` and `ed25519:` fields are not
in that no-slash set. A case-insensitive `/root` followed by slash or end of
value is rejected wherever it occurs. Token boundaries and decoded JWT
structure keep benign `risk-score`, `release-2026.08.30`, `v1.20.30-beta`, and
`release-1.2.3.4` values outside those canary classes. Fixed
patterns remain chunk-boundary complete and diagnostics reveal only the closed
`sanitizer-rejected` category. Determinism assumes the same parent receipt,
asserted nonce-source label, and nonce bytes.

<!-- codex-exec-v0-contract:adaptation-flow:begin -->
Adaptation flow contract: the ordered steps are `adapt-parent`,
`sanitize-child`, `adapt-exact-child`, `build-owner-private-sidecar`,
`consume-publication-authority`, `independently-readapt-pair`,
`begin-filesystem-publication`.
<!-- codex-exec-v0-contract:adaptation-flow:end -->

The CLI command is `adapt-codex-exec-v0`. It requires explicit
`--raw-stdout-jsonl`, `--authority-receipt`, `--trusted-context`,
`--output-type private|shareable-sanitized`, and `--output` paths. Shareable
mode accepts a selected synthetic or genuine parent capture with its parent
receipt and context; imported evidence and nonce-source fields remain asserted
declarations. The sealed owner draws both local entropy roles, adapts and
sanitizes the parent, consumes the mint to construct the owner-private sidecar
and authoritative public bundle together, and imports the completed pair to
independently re-adapt and validate the child before filesystem publication.

Only an attempted `adapt-codex-exec-v0` command uses closed argument
diagnostics, so attacker-bearing argv/path values are never echoed. Unrelated
commands retain Clap's detailed usage and exit-2 behavior; help and version
remain successful.

<!-- codex-exec-v0-contract:anonymous-publication:begin -->
Publication staging contract: temporary storage is `same-directory-o-tmpfile`
with mode `0600`; checks are `owner`, `type`, `link-count`, `content`,
`stable-metadata`, followed by `sync-file`, `sync-directory`.
<!-- codex-exec-v0-contract:anonymous-publication:end -->
<!-- codex-exec-v0-contract:pair-order:begin -->
Pair order contract: the precondition `validate-semantic-pair` occurs before all six
filesystem phases; the phases are `prepare-owner-private-sidecar`, `prepare-public-output`, `link-owner-private-sidecar`, `revalidate-committed-sidecar-immediately-before-public-link`, `link-public-output`, `revalidate-sidecar-and-public-output`.
<!-- codex-exec-v0-contract:pair-order:end -->
<!-- codex-exec-v0-contract:commit-point:begin -->
Commit contract: `linkat` uses `no-clobber` replacement semantics, and the
commit point is `successful-link`.
<!-- codex-exec-v0-contract:commit-point:end -->

On Linux, inputs and every traversed parent component must not be symlinks;
inputs must be regular files. Opened and path `(dev,ino)` identities are
compared, hard-link aliases are rejected, and pre/post-read size/time/inode
metadata detects observable concurrent mutation. Output ancestors are walked
and pinned with `openat` directory descriptors. The publisher opens an
anonymous same-directory `O_TMPFILE`, writes all bytes, sets and verifies
owner-only mode `0600`, verifies owner/type/link-count, content digest, and
stable metadata, syncs the file and directory, then publishes with `linkat`
from the verified procfs descriptor path. The successful no-clobber `linkat`
is the commit point; an incumbent name is never overwritten.

For a shareable pair, semantic pair validation runs before filesystem work.
The owner-private sidecar is prepared and linked first. Immediately before the
public link, the protected guard revalidates the committed sidecar. After the
public link attempt, the transaction performs final sidecar and public
identity/integrity checks and retains the documented
identity-over-integrity-over-durability error precedence.

<!-- codex-exec-v0-contract:publication-uncertainty:begin -->
Uncertainty contract: before commit, `no-created-final-name`; after commit,
`linked-name-may-remain-on-failure` with classes
`output-identity-uncertain`, `output-integrity-uncertain`,
`durability-uncertain`; cleanup is `do-not-remove-linked-name`.
<!-- codex-exec-v0-contract:publication-uncertainty:end -->

Before a successful link, failure drops an anonymous, unlinked inode and this
operation has created no final name; an existing incumbent remains untouched.
After a successful link, the final name may exist even when source-identity,
directory-sync, final-name identity, or held-content checks fail. Those
post-link failures are reported respectively through closed
`output-identity-uncertain`, `output-integrity-uncertain`, or
`durability-uncertain` classes, and the publisher does not remove the linked
name. Success and failure emit no structured stdout. The executable sends only
`AdapterErrorV0::code().as_str()` to the global stderr sink, never the error's
diagnostic string.

Output-set failure cleanup removes members through the held staging descriptor.
Before removing the parent-relative staging name, it freshly proves that name
still identifies the captured owner-only directory, proves the held directory's
identity/type/owner/mode, and inventories it as empty. The deterministic
post-cleanup substitution schedule preserves an empty replacement installed at
the old name and returns `output-rollback-uncertain`. Linux provides no
unlink-by-open-directory-descriptor operation, so an unconstrained same-UID
writer in the final `statat`/held-inventory-to-`unlinkat` syscall interval is
outside the replacement-preservation claim.

Multi-output rollback first verifies the final name and then atomically moves
whatever occupies it to a fresh no-replace quarantine name. A post-rename
identity check permits removal only when the quarantined inode is the held
publication; a replacement raced into the old name is retained in quarantine
and reported as `output-rollback-uncertain`. Linux has no unlink-by-open-file
descriptor operation, so the final cleanup of the random quarantine name does
not claim safety against a same-UID writer that discovers and replaces that
name in the remaining check-to-unlink interval. That adversary is outside this
narrow deletion claim; all detected ambiguity remains fail-closed.

This publication contract assumes a Linux kernel, procfs, filesystem, and
mount profile supporting the verified `O_TMPFILE` and `linkat` operations.
Pinned descriptors prevent path redirection within the implemented walk, but
the contract does not claim protection from a hostile kernel/filesystem,
power-loss semantics beyond successful syncs, or temporal integrity after the
returned handles are dropped. Other operating systems are unsupported.

## Threat boundary and nonclaims

The adapter implements deterministic translation for the declared, captured,
version-pinned subset relative to the exact authorized bytes, private receipt,
and out-of-band expected commitment/context. Its trajectory evidence labels are
referential: `cites-raw-range` checks only exact range/digest integrity, and
`declared-derivation-binding` checks only that a binding and nonempty source
inputs were declared. The generic validator does not decode a cited range,
execute a declared derivation, or compare either result with the normalized
value. Semantic value-to-source binding therefore remains an adapter-specific
obligation; replay-authority verification neither completes it nor introduces
a generic decoder. The adapter also does not establish
source completeness or truth, absence of activity omitted before JSONL,
behavior outside the capture, authenticity when bytes/receipt/trusted context
are all replaced, pre-capture integrity, remote attestation, complete
mediation, hidden intent or chain-of-thought access, sandbox effectiveness,
absence of side effects, privacy merely because sanitization ran, policy
correctness, governance legitimacy, enforcement, temporal safety, causality,
concurrency, principals, capabilities, delegation, leases, liveness,
recoverability, or incident diagnosis. Publication additionally requires the
closed shareable type, complete staged-surface scan, and human review. A
rejected-event report is diagnostic only and never a partial certificate.
