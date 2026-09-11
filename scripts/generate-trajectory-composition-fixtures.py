#!/usr/bin/env python3
"""Generate exact trajectory fixtures and their Lean event projection."""

from __future__ import annotations

import argparse
import hashlib
import json
import struct
import tomllib
from pathlib import Path


HASH_ENVELOPE = b"legitimacy.trajectory.hash.v0\0"
TRACE_MAGIC = b"legitimacy.trajectory.trace.canonical.v0\0"
POLICY_ID = "policy.trajectory-composition.peer-half"
POLICY_VERSION = "0"


def frame(value: bytes) -> bytes:
    return struct.pack(">Q", len(value)) + value


def framed_sha256(domain: str, components: list[bytes]) -> str:
    payload = HASH_ENVELOPE + frame(domain.encode()) + struct.pack(">Q", len(components))
    payload += b"".join(frame(component) for component in components)
    return "sha256:" + hashlib.sha256(payload).hexdigest()


def put_string(value: str) -> bytes:
    return frame(value.encode())


def encode_binding(binding: dict[str, object]) -> bytes:
    return b"".join(put_string(str(binding[key])) for key in ("identity", "version", "hash"))


def locator(record: bytes, index: int) -> dict[str, object]:
    return {
        "record_index": index,
        "byte_offset": 0,
        "byte_length": len(record),
        "digest": framed_sha256("legitimacy.trajectory.source-locator.v0", [record]),
    }


def cited(value: object, record: bytes, index: int) -> dict[str, object]:
    return {
        "value": value,
        "evidence": {"classification": "cites-raw-range", "locator": locator(record, index)},
    }


def encode_locator(value: dict[str, object]) -> bytes:
    return (
        struct.pack(">Q", int(value["record_index"]))
        + struct.pack(">Q", int(value["byte_offset"]))
        + struct.pack(">Q", int(value["byte_length"]))
        + put_string(str(value["digest"]))
    )


def encode_cited(value: object, encode_value, evidence: dict[str, object]) -> bytes:
    return b"\x01" + encode_value(value) + b"\x00" + encode_locator(evidence["locator"])


def canonical_event(event: dict[str, object]) -> bytes:
    output = encode_cited(
        event["event_id"]["value"], put_string, event["event_id"]["evidence"]
    )
    output += encode_cited(
        event["sequence_index"]["value"],
        lambda value: struct.pack(">Q", int(value)),
        event["sequence_index"]["evidence"],
    )
    output += encode_cited(
        event["kind"]["value"], put_string, event["kind"]["evidence"]
    )
    source = event["source_item_id"]
    if source is None:
        output += b"\x00"
    else:
        output += b"\x01" + encode_cited(
            source["value"], put_string, source["evidence"]
        )
    output += struct.pack(">Q", int(event["raw_record"]["record_index"]))
    output += put_string(str(event["raw_record"]["digest"]))
    output += struct.pack(">Q", 0)
    return output


def canonical_trace(trace: dict[str, object]) -> tuple[bytes, list[bytes]]:
    header = TRACE_MAGIC + encode_binding(trace["schema"])
    header += encode_cited(
        trace["run_id"]["value"], put_string, trace["run_id"]["evidence"]
    )
    header += encode_binding(trace["adapter"])
    header += encode_binding(trace["policy"])
    header += struct.pack(">Q", int(trace["raw_capture"]["record_count"]))
    header += put_string(str(trace["raw_capture"]["digest"]))
    header += struct.pack(">Q", len(trace["events"]))
    events = [canonical_event(event) for event in trace["events"]]
    return header + b"".join(events), events


def replay_values(trace: dict[str, object]) -> tuple[str, list[str], str]:
    canonical, canonical_events = canonical_trace(trace)
    trajectory_digest = framed_sha256("legitimacy.trajectory.trace.v0", [canonical])
    record_count = len(trace["events"])
    raw_capture = trace["raw_capture"]
    genesis = framed_sha256(
        "legitimacy.trajectory.replay.genesis.v0",
        [
            b"legitimacy.trajectory.replay",
            b"0",
            str(trace["schema"]["identity"]).encode(),
            str(trace["schema"]["version"]).encode(),
            str(trace["schema"]["hash"]).encode(),
            str(trace["adapter"]["identity"]).encode(),
            str(trace["adapter"]["version"]).encode(),
            str(trace["adapter"]["hash"]).encode(),
            str(trace["policy"]["identity"]).encode(),
            str(trace["policy"]["version"]).encode(),
            str(trace["policy"]["hash"]).encode(),
            struct.pack(">Q", int(raw_capture["record_count"])),
            str(raw_capture["digest"]).encode(),
            trajectory_digest.encode(),
            struct.pack(">Q", record_count),
        ],
    )
    canonical_digests = [
        framed_sha256("legitimacy.trajectory.replay.canonical-event.v0", [event])
        for event in canonical_events
    ]
    previous = genesis
    for event, canonical_digest in zip(trace["events"], canonical_digests, strict=True):
        previous = framed_sha256(
            "legitimacy.trajectory.replay.chain-step.v0",
            [
                previous.encode(),
                struct.pack(">Q", int(event["sequence_index"]["value"])),
                str(event["event_id"]["value"]).encode(),
                str(event["raw_record"]["digest"]).encode(),
                canonical_digest.encode(),
            ],
        )
    return trajectory_digest, canonical_digests, previous


def compact_json(value: object) -> bytes:
    return json.dumps(value, separators=(",", ":"), ensure_ascii=True).encode() + b"\n"


def validate_policy(policy_bytes: bytes) -> None:
    policy = tomllib.loads(policy_bytes.decode())
    expected = {
        "policy_format": "legitimacy.trajectory-composition.policy",
        "policy_format_version": "0",
        "policy_identity": POLICY_ID,
        "policy_version": POLICY_VERSION,
        "occurrence_encoder_identity": "legitimacy.trajectory-composition.occurrence-index-strength",
        "occurrence_encoder_version": "0",
        "historical_property_identity": "legitimacy.trajectory-composition.every-observed-prefix-green",
        "historical_property_version": "0",
    }
    for key, value in expected.items():
        if policy.get(key) != value:
            raise ValueError(f"unsupported canonical policy field: {key}")
    if policy.get("graph") != {"name": "trajectory-composition-peer-half", "version": "0"}:
        raise ValueError("unsupported canonical graph metadata")
    if policy.get("edges", []) != [] or len(policy.get("nodes", [])) != 1:
        raise ValueError("unsupported canonical graph topology")
    node = policy["nodes"][0]
    expected_node = {
        "id": "peer-half",
        "type": "binary",
        "name": "peer-half",
        "default": "deny",
        "combination": "first_match",
        "gates": [
            {
                "type": "peer_relative",
                "field": "strength",
                "percentile": 0.5,
                "decision": "permit",
            }
        ],
    }
    if node != expected_node:
        raise ValueError("unsupported canonical graph node")


def write_fixture(
    output_root: Path,
    name: str,
    kinds: list[str],
    schema: dict[str, object],
    adapter: dict[str, object],
    policy: dict[str, object],
) -> dict[str, object]:
    records = [
        compact_json({"fixture": name, "occurrence": index}).rstrip(b"\n")
        for index in range(len(kinds))
    ]
    raw_capture = {
        "record_count": len(records),
        "digest": framed_sha256("legitimacy.trajectory.raw-capture.v0", records),
    }
    events = []
    for index, (record, kind) in enumerate(zip(records, kinds, strict=True)):
        events.append(
            {
                "event_id": cited(f"{name}-event-{index}", record, index),
                "sequence_index": cited(index, record, index),
                "kind": cited(kind, record, index),
                "source_item_id": cited("repeated-source-item", record, index),
                "raw_record": {
                    "record_index": index,
                    "digest": framed_sha256(
                        "legitimacy.trajectory.raw-record.v0", [record]
                    ),
                },
                "payload": {},
            }
        )
    trace = {
        "schema": schema,
        "run_id": cited(f"trajectory-composition-{name}", records[0], 0),
        "adapter": adapter,
        "policy": policy,
        "raw_capture": raw_capture,
        "events": events,
    }
    context = {
        "declarations_format": "legitimacy.trajectory.validation-declarations",
        "declarations_version": "0",
        "adapter": adapter,
        "policy": policy,
        "raw_capture": raw_capture,
        "allowed_derivations": [],
    }
    raw_set = {
        "record_set_format": "legitimacy.trajectory.exact-raw-record-set",
        "record_set_version": "0",
        "records": [record.decode() for record in records],
    }
    directory = output_root / "fixtures" / "trajectory-composition-v0" / name
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "raw-records.json").write_bytes(compact_json(raw_set))
    trace_bytes = compact_json(trace)
    (directory / "trace.json").write_bytes(trace_bytes)
    (directory / "declared-context.json").write_bytes(compact_json(context))
    trajectory_digest, canonical_digests, final_head = replay_values(trace)
    return {
        "name": name,
        "trace": trace,
        "trace_file_sha256": hashlib.sha256(trace_bytes).hexdigest(),
        "trajectory_digest": trajectory_digest,
        "canonical_event_digests": canonical_digests,
        "replay_final_head": final_head,
    }


def lean_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=True)


def lean_kind(value: str) -> str:
    return {
        "action-request": ".actionRequest",
        "action-result": ".actionResult",
        "observation": ".observation",
        "message": ".message",
        "lifecycle": ".lifecycle",
    }[value]


def lean_event(event: dict[str, object], canonical_digest: str) -> str:
    source = event["source_item_id"]["value"]
    return (
        "  { eventId := "
        + lean_string(str(event["event_id"]["value"]))
        + "\n    kind := "
        + lean_kind(str(event["kind"]["value"]))
        + "\n    sourceItemId := some "
        + lean_string(str(source))
        + "\n    rawRecordDigest := "
        + lean_string(str(event["raw_record"]["digest"]))
        + "\n    canonicalEventDigest := "
        + lean_string(canonical_digest)
        + " }"
    )


def write_lean_projection(
    output_root: Path,
    policy_bytes: bytes,
    fixtures: list[dict[str, object]],
) -> None:
    policy_digest = framed_sha256("legitimacy.trajectory.artifact.v0", [policy_bytes])
    policy_sha = hashlib.sha256(policy_bytes).hexdigest()
    fixture_defs = []
    for fixture in fixtures:
        name = str(fixture["name"])
        prefix = "benign" if name == "benign" else "red"
        events = fixture["trace"]["events"]
        rendered = ",\n".join(
            lean_event(event, digest)
            for event, digest in zip(
                events, fixture["canonical_event_digests"], strict=True
            )
        )
        fixture_defs.append(
            f"""def {prefix}TrajectoryEventsV0 : List NormalizedEventOccurrenceV0 :=
[
{rendered}
]

def {prefix}TrajectoryDigestV0 : String := {lean_string(str(fixture['trajectory_digest']))}
def {prefix}ReplayFinalHeadV0 : String := {lean_string(str(fixture['replay_final_head']))}
def {prefix}TraceFileSha256V0 : String := {lean_string(str(fixture['trace_file_sha256']))}
"""
        )
    module = f"""/- This file is generated by scripts/generate-trajectory-composition-fixtures.py. -/
import Legitimacy.Protocol.TrajectoryComposition
import Legitimacy.Results.NonPeerRelative

set_option autoImplicit false

namespace Legitimacy

def generatedTrajectoryPolicyIdentityV0 : String := {lean_string(POLICY_ID)}
def generatedTrajectoryPolicyVersionV0 : String := {lean_string(POLICY_VERSION)}
def generatedTrajectoryPolicyArtifactDigestV0 : String := {lean_string(policy_digest)}
def generatedTrajectoryPolicySourceSha256V0 : String := {lean_string(policy_sha)}
def generatedTrajectoryOccurrenceEncoderIdentityV0 : String :=
  "legitimacy.trajectory-composition.occurrence-index-strength"
def generatedTrajectoryOccurrenceEncoderVersionV0 : String := "0"
def generatedTrajectoryHistoricalPropertyIdentityV0 : String :=
  "legitimacy.trajectory-composition.every-observed-prefix-green"
def generatedTrajectoryHistoricalPropertyVersionV0 : String := "0"

def generatedTrajectoryCompiledGovernanceV0 : CompiledGovernance :=
  peerGraphSacrificedCompiledGovernance

theorem generatedTrajectoryPolicy_graph_eq_peerGraph :
    generatedTrajectoryCompiledGovernanceV0.graph = peerGraph := rfl

/-- Exact-rational half comparison used by the generated Lean peer policy. -/
theorem generatedTrajectoryRationalHalfCriterionV0
    (rank total : Nat) (htotal : 0 < total) :
    ((rank : ℚ) / (total : ℚ) ≥ (1 : ℚ) / 2) ↔ 2 * rank ≥ total := by
  have htotalQ : (0 : ℚ) < total := by exact_mod_cast htotal
  constructor
  · intro h
    have hmul : (1 : ℚ) / 2 * total ≤ rank := (le_div_iff₀ htotalQ).1 h
    have hscaled : (total : ℚ) ≤ 2 * rank := by linarith
    exact_mod_cast hscaled
  · intro h
    have hscaled : (total : ℚ) ≤ 2 * rank := by exact_mod_cast h
    have hmul : (1 : ℚ) / 2 * total ≤ rank := by linarith
    exact (le_div_iff₀ htotalQ).2 hmul

/-- The selected compiled graph permits an encoded prefix occurrence exactly at rational half-rank. -/
theorem generatedTrajectoryEncodedPrefixPermitIffRationalHalfV0
    (events : List NormalizedEventOccurrenceV0)
    (prefixLength : Nat)
    (hprefixNonempty : 0 < prefixLength)
    (hprefixInRange : prefixLength ≤ events.length)
    (claim : ClaimQ)
    (hclaimInPrefix : claim ∈ (encodedClaims events).take prefixLength) :
    graphDecide generatedTrajectoryCompiledGovernanceV0.graph
        ((encodedClaims events).take prefixLength) claim.id =
          BinaryDecision.Permit ↔
      ((countAtMost ((encodedClaims events).take prefixLength)
          claim.strength : Nat) : ℚ) /
          (((encodedClaims events).take prefixLength).length : ℚ) ≥
        (1 : ℚ) / 2 := by
  have hclaimsLength :
      ((encodedClaims events).take prefixLength).length = prefixLength := by
    simp [hprefixInRange]
  have hclaimsNonempty :
      0 < ((encodedClaims events).take prefixLength).length := by
    omega
  have hclaimsDistinct :
      ClaimsDistinct ((encodedClaims events).take prefixLength) := by
    unfold ClaimsDistinct
    exact
      ((List.take_sublist prefixLength (encodedClaims events)).map Claim.id).nodup
        (by
          simpa [ClaimsDistinct] using encodedClaims_distinct events)
  have hlookup :
      lookupStrength claim.id ((encodedClaims events).take prefixLength) =
        claim.strength :=
    lookupStrength_eq_of_mem_distinct hclaimsDistinct hclaimInPrefix
  rw [generatedTrajectoryPolicy_graph_eq_peerGraph]
  simp only [peerGraph, graphDecide, peerRelativeNode, hlookup]
  rw [generatedTrajectoryRationalHalfCriterionV0
    (countAtMost ((encodedClaims events).take prefixLength) claim.strength)
    ((encodedClaims events).take prefixLength).length hclaimsNonempty]
  split <;> simp_all

{''.join(fixture_defs)}
theorem benignTrajectoryClaimsDistinctV0 :
    ClaimsDistinct (encodedClaims benignTrajectoryEventsV0) :=
  encodedClaims_distinct benignTrajectoryEventsV0

theorem benignTrajectorySingletonsPermitV0 :
    allSingletonsPermitBool generatedTrajectoryCompiledGovernanceV0
      benignTrajectoryEventsV0 = true := by native_decide

theorem benignTrajectoryFirstBadPrefixV0 :
    firstBadPrefix? generatedTrajectoryCompiledGovernanceV0 benignTrajectoryEventsV0 = none := by
  native_decide

theorem benignTrajectoryEveryObservedPrefixGreenV0 :
    EveryObservedPrefixGreen generatedTrajectoryCompiledGovernanceV0 benignTrajectoryEventsV0 :=
  (firstBadPrefix_none_iff generatedTrajectoryCompiledGovernanceV0 benignTrajectoryEventsV0).1
    benignTrajectoryFirstBadPrefixV0

theorem redTrajectoryClaimsDistinctV0 :
    ClaimsDistinct (encodedClaims redTrajectoryEventsV0) :=
  encodedClaims_distinct redTrajectoryEventsV0

theorem redTrajectorySingletonsPermitV0 :
    allSingletonsPermitBool generatedTrajectoryCompiledGovernanceV0
      redTrajectoryEventsV0 = true := by native_decide

theorem redTrajectoryFirstBadPrefixV0 :
    firstBadPrefix? generatedTrajectoryCompiledGovernanceV0 redTrajectoryEventsV0 =
      some {{ transitionIndex := 2, prefixLength := 3, deniedOccurrenceIndex := 0 }} := by
  native_decide

theorem redTrajectoryNotEveryObservedPrefixGreenV0 :
    ¬ EveryObservedPrefixGreen generatedTrajectoryCompiledGovernanceV0
      redTrajectoryEventsV0 := by
  intro hgreen
  have hnone :=
    (firstBadPrefix_none_iff generatedTrajectoryCompiledGovernanceV0 redTrajectoryEventsV0).2
      hgreen
  rw [redTrajectoryFirstBadPrefixV0] at hnone
  contradiction

end Legitimacy
"""
    path = (
        output_root
        / "lean"
        / "Legitimacy"
        / "Protocol"
        / "TrajectoryCompositionGenerated"
        / "Fixtures.lean"
    )
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(module)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--repository-root", type=Path, required=True)
    args = parser.parse_args()
    repository_root = args.repository_root.resolve()
    output_root = args.output_root.resolve()
    policy_bytes = (
        repository_root / "fixtures" / "trajectory-composition-v0" / "policy.toml"
    ).read_bytes()
    validate_policy(policy_bytes)
    adapter_bytes = (
        repository_root / "fixtures" / "trajectory-composition-v0" / "adapter.txt"
    ).read_bytes()
    schema_bytes = (repository_root / "schemas" / "trajectory-v0.schema.json").read_bytes()
    schema = {
        "identity": "legitimacy.trajectory.trace",
        "version": "0",
        "hash": framed_sha256("legitimacy.trajectory.artifact.v0", [schema_bytes]),
    }
    adapter = {
        "identity": "adapter.trajectory-composition-fixture",
        "version": "0",
        "hash": framed_sha256("legitimacy.trajectory.artifact.v0", [adapter_bytes]),
    }
    policy = {
        "identity": POLICY_ID,
        "version": POLICY_VERSION,
        "hash": framed_sha256("legitimacy.trajectory.artifact.v0", [policy_bytes]),
    }
    fixtures = [
        write_fixture(output_root, "benign", ["observation", "message"], schema, adapter, policy),
        write_fixture(
            output_root,
            "red",
            ["action-request", "action-result", "lifecycle"],
            schema,
            adapter,
            policy,
        ),
    ]
    write_lean_projection(output_root, policy_bytes, fixtures)


if __name__ == "__main__":
    main()
