#!/usr/bin/env python3
"""Independent standard-library implementation for the committed replay vector."""

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
HASH_ENVELOPE = b"legitimacy.trajectory.hash.v0\0"
CANONICAL_MAGIC = b"legitimacy.trajectory.trace.canonical.v0\0"


def u64(value):
    return value.to_bytes(8, "big")


def frame(value):
    return u64(len(value)) + value


def text(value):
    return frame(value.encode("utf-8"))


def framed_hash(domain, components):
    preimage = HASH_ENVELOPE + frame(domain.encode("ascii")) + u64(len(components))
    preimage += b"".join(frame(component) for component in components)
    return "sha256:" + hashlib.sha256(preimage).hexdigest()


def binding(value):
    return text(value["identity"]) + text(value["version"]) + text(value["hash"])


def locator(value):
    return (
        u64(value["record_index"])
        + u64(value["byte_offset"])
        + u64(value["byte_length"])
        + text(value["digest"])
    )


def evidence(value):
    classification = value["classification"]
    if classification == "cites-raw-range":
        return b"\x00" + locator(value["locator"])
    if classification == "declared-derivation-binding":
        inputs = value["source_inputs"]
        return b"\x01" + binding(value["rule"]) + u64(len(inputs)) + b"".join(
            locator(item) for item in inputs
        )
    if classification == "unavailable":
        return b"\x02" + text(value["reason"])
    raise ValueError("unknown evidence classification")


def evidenced(value, encode):
    present = value["value"] is not None
    encoded = b"\x01" + encode(value["value"]) if present else b"\x00"
    return encoded + evidence(value["evidence"])


def normalized(value):
    kind = value["type"]
    if kind == "null":
        return b"\x00"
    if kind == "boolean":
        return b"\x01" + bytes([value["value"]])
    if kind == "integer":
        return b"\x02" + text(value["value"])
    if kind == "string":
        return b"\x03" + text(value["value"])
    if kind == "array":
        items = value["value"]
        return b"\x04" + u64(len(items)) + b"".join(normalized(item) for item in items)
    if kind == "object":
        items = sorted(value["value"].items())
        return b"\x05" + u64(len(items)) + b"".join(
            text(key) + normalized(item) for key, item in items
        )
    raise ValueError("unknown normalized value kind")


def canonical_event(event):
    output = evidenced(event["event_id"], text)
    output += evidenced(event["sequence_index"], u64)
    output += evidenced(event["kind"], text)
    if event["source_item_id"] is None:
        output += b"\x00"
    else:
        output += b"\x01" + evidenced(event["source_item_id"], text)
    output += u64(event["raw_record"]["record_index"])
    output += text(event["raw_record"]["digest"])
    items = sorted(event["payload"].items())
    output += u64(len(items))
    output += b"".join(text(key) + evidenced(item, normalized) for key, item in items)
    return output


def canonical_header(trace):
    output = CANONICAL_MAGIC + binding(trace["schema"])
    output += evidenced(trace["run_id"], text)
    output += binding(trace["adapter"]) + binding(trace["policy"])
    output += u64(trace["raw_capture"]["record_count"])
    output += text(trace["raw_capture"]["digest"])
    return output + u64(len(trace["events"]))


def replay_vector(trace):
    event_bytes = [canonical_event(event) for event in trace["events"]]
    canonical = canonical_header(trace) + b"".join(event_bytes)
    trajectory_digest = framed_hash("legitimacy.trajectory.trace.v0", [canonical])
    count = len(trace["events"])
    genesis_components = [
        b"legitimacy.trajectory.replay",
        b"0",
        trace["schema"]["identity"].encode(),
        trace["schema"]["version"].encode(),
        trace["schema"]["hash"].encode(),
        trace["adapter"]["identity"].encode(),
        trace["adapter"]["version"].encode(),
        trace["adapter"]["hash"].encode(),
        trace["policy"]["identity"].encode(),
        trace["policy"]["version"].encode(),
        trace["policy"]["hash"].encode(),
        u64(trace["raw_capture"]["record_count"]),
        trace["raw_capture"]["digest"].encode(),
        trajectory_digest.encode(),
        u64(count),
    ]
    genesis = framed_hash("legitimacy.trajectory.replay.genesis.v0", genesis_components)
    previous = genesis
    records = []
    for event, encoded in zip(trace["events"], event_bytes):
        sequence = event["sequence_index"]["value"]
        event_id = event["event_id"]["value"]
        raw_digest = event["raw_record"]["digest"]
        event_digest = framed_hash(
            "legitimacy.trajectory.replay.canonical-event.v0", [encoded]
        )
        resulting = framed_hash(
            "legitimacy.trajectory.replay.chain-step.v0",
            [
                previous.encode(),
                u64(sequence),
                event_id.encode(),
                raw_digest.encode(),
                event_digest.encode(),
            ],
        )
        records.append(
            {
                "sequence_index": sequence,
                "event_id": event_id,
                "raw_record_digest": raw_digest,
                "canonical_event_digest": event_digest,
                "previous_head": previous,
                "resulting_head": resulting,
            }
        )
        previous = resulting
    replay = {
        "replay_format": "legitimacy.trajectory.replay",
        "replay_version": "0",
        "schema": trace["schema"],
        "adapter": trace["adapter"],
        "policy": trace["policy"],
        "raw_capture": trace["raw_capture"],
        "trajectory_digest": trajectory_digest,
        "record_count": count,
        "genesis_head": genesis,
        "records": records,
        "final_head": previous,
    }
    return canonical, (json.dumps(replay, separators=(",", ":"), ensure_ascii=False) + "\n").encode()


def main():
    trace = json.loads((ROOT / "trace.json").read_bytes())
    canonical, replay = replay_vector(trace)
    assert canonical == (ROOT / "canonical-trace.bin").read_bytes()
    assert replay == (ROOT / "replay.json").read_bytes()
    assert hashlib.sha256(canonical).hexdigest() == "245fb1d661b5a3a6831317407f04bfdf5b1f777adb28adcd9f6b27e51ed76850"
    assert hashlib.sha256(replay).hexdigest() == "54ef8ec5d3a49eaa0d1eee0066696d363ccb0b945937c05f69d3d17a01b519f8"
    print("trajectory replay reference vector: OK")


if __name__ == "__main__":
    main()
