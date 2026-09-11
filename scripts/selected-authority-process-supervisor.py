#!/usr/bin/env python3
"""Bounded Linux descendant-tree execution for the selected-authority gate."""

from __future__ import annotations

import argparse
import ctypes
import errno
import os
import selectors
import signal
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path


READ_CHUNK_BYTES = 64 * 1024
POLL_INTERVAL_SECONDS = 0.005
CLEANUP_CAP_SECONDS = 10.0
PUBLICATION_MARGIN_SECONDS = 1.0
STATUS_MAGIC = "legitimacy.selected-authority-process.v2"
PR_SET_CHILD_SUBREAPER = 36


@dataclass(frozen=True, order=True)
class ProcessIdentity:
    pid: int
    start_time: int


@dataclass
class StreamState:
    descriptor: int
    output: int
    cap: int
    total: int = 0
    retained: int = 0
    eof: bool = False


@dataclass
class SupervisionState:
    pid: int
    raw_wait_status: int | None = None
    reaped_descendants: int = 0
    term_sent: bool = False
    kill_sent: bool = False
    observed_descendants: set[ProcessIdentity] = field(default_factory=set)
    term_signaled: set[ProcessIdentity] = field(default_factory=set)
    cleanup_errors: list[str] = field(default_factory=list)

    def record_error(self, label: str) -> None:
        if label not in self.cleanup_errors:
            self.cleanup_errors.append(label)


def positive_integer(value: str) -> int:
    parsed = int(value, 10)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("value must be positive")
    return parsed


def nonnegative_integer(value: str) -> int:
    parsed = int(value, 10)
    if parsed < 0:
        raise argparse.ArgumentTypeError("value must be nonnegative")
    return parsed


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument("--timeout-ms", required=True, type=positive_integer)
    parser.add_argument("--term-grace-ms", required=True, type=positive_integer)
    parser.add_argument("--stdout-cap", required=True, type=nonnegative_integer)
    parser.add_argument("--stderr-cap", required=True, type=nonnegative_integer)
    parser.add_argument("--stdout", required=True, type=Path)
    parser.add_argument("--stderr", required=True, type=Path)
    parser.add_argument("--status", required=True, type=Path)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    arguments = parser.parse_args()
    if not arguments.command or arguments.command[0] != "--" or len(arguments.command) == 1:
        parser.error("an exact command must follow --")
    arguments.command = arguments.command[1:]
    return arguments


def monotonic_deadline(milliseconds: int) -> float:
    return time.monotonic() + (milliseconds / 1000.0)


def create_output(path: Path) -> int:
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    return os.open(path, flags, 0o600)


def write_all(descriptor: int, content: bytes, deadline: float | None = None) -> None:
    offset = 0
    while offset < len(content):
        if deadline is not None and time.monotonic() >= deadline:
            raise TimeoutError("publication deadline")
        try:
            count = os.write(descriptor, content[offset:])
        except InterruptedError:
            continue
        if count <= 0:
            raise OSError(errno.EIO, "short write")
        offset += count


def set_subreaper() -> None:
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(PR_SET_CHILD_SUBREAPER, 1, 0, 0, 0) != 0:
        error = ctypes.get_errno()
        raise OSError(error, os.strerror(error))


def close_descriptor(descriptor: int) -> None:
    try:
        os.close(descriptor)
    except OSError:
        pass


def close_descriptors(descriptors: list[int]) -> None:
    for descriptor in descriptors:
        close_descriptor(descriptor)


def spawn_group(command: list[str]) -> tuple[SupervisionState, int, int, int, int]:
    stdout_read, stdout_write = os.pipe2(os.O_CLOEXEC)
    stderr_read, stderr_write = os.pipe2(os.O_CLOEXEC)
    ready_read, ready_write = os.pipe2(os.O_CLOEXEC)
    release_read, release_write = os.pipe2(os.O_CLOEXEC)
    descriptors = [
        stdout_read,
        stdout_write,
        stderr_read,
        stderr_write,
        ready_read,
        ready_write,
        release_read,
        release_write,
    ]
    try:
        pid = os.fork()
    except BaseException:
        close_descriptors(descriptors)
        raise
    if pid == 0:
        close_descriptors([stdout_read, stderr_read, ready_read, release_write])
        try:
            os.setsid()
            write_all(ready_write, b"R")
            close_descriptor(ready_write)
            while True:
                try:
                    release = os.read(release_read, 1)
                    break
                except InterruptedError:
                    continue
            close_descriptor(release_read)
            if release != b"G":
                os._exit(126)
            os.dup2(stdout_write, sys.stdout.fileno(), inheritable=True)
            os.dup2(stderr_write, sys.stderr.fileno(), inheritable=True)
            close_descriptors([stdout_write, stderr_write])
            os.execvpe(command[0], command, os.environ)
        except BaseException as error:
            try:
                message = f"selected-authority child exec: {type(error).__name__}\n".encode()
                write_all(sys.stderr.fileno(), message)
            except BaseException:
                pass
            os._exit(127)

    close_descriptors([stdout_write, stderr_write, ready_write, release_read])
    for descriptor in [stdout_read, stderr_read, ready_read, release_write]:
        os.set_blocking(descriptor, False)
    return SupervisionState(pid=pid), stdout_read, stderr_read, ready_read, release_write


def group_exists(pid: int) -> bool:
    try:
        os.killpg(pid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError as error:
        raise RuntimeError("process-group permission") from error


def process_identity(pid: int) -> ProcessIdentity | None:
    try:
        content = Path(f"/proc/{pid}/stat").read_text(encoding="ascii")
    except FileNotFoundError:
        return None
    closing = content.rfind(")")
    if closing < 0:
        raise RuntimeError("process stat syntax")
    fields = content[closing + 2 :].split()
    if len(fields) <= 19:
        raise RuntimeError("process stat fields")
    return ProcessIdentity(pid, int(fields[19], 10))


def identity_exists(identity: ProcessIdentity) -> bool:
    return process_identity(identity.pid) == identity


def child_pids(pid: int) -> list[int]:
    try:
        content = Path(f"/proc/{pid}/task/{pid}/children").read_text(encoding="ascii")
    except FileNotFoundError:
        return []
    if not content.strip():
        return []
    return [int(value, 10) for value in content.split()]


def observe_descendants(state: SupervisionState) -> set[ProcessIdentity]:
    pending = child_pids(os.getpid())
    visited: set[int] = set()
    current: set[ProcessIdentity] = set()
    while pending:
        pid = pending.pop()
        if pid in visited:
            continue
        visited.add(pid)
        identity = process_identity(pid)
        if identity is None:
            continue
        current.add(identity)
        pending.extend(child_pids(pid))
    state.observed_descendants.update(
        identity for identity in current if identity.pid != state.pid
    )
    return current


def reap_available(state: SupervisionState) -> None:
    while True:
        try:
            waited, raw_status = os.waitpid(-1, os.WNOHANG)
        except ChildProcessError:
            return
        except InterruptedError:
            continue
        if waited == 0:
            return
        if waited == state.pid:
            state.raw_wait_status = raw_status
        else:
            state.reaped_descendants += 1


def descendants_absent(state: SupervisionState) -> bool:
    current = observe_descendants(state)
    if any(identity.pid != state.pid for identity in current):
        return False
    return not any(identity_exists(identity) for identity in state.observed_descendants)


def drain_stream(stream: StreamState) -> str | None:
    while True:
        try:
            content = os.read(stream.descriptor, READ_CHUNK_BYTES)
        except BlockingIOError:
            return None
        except InterruptedError:
            continue
        if not content:
            stream.eof = True
            return None
        stream.total += len(content)
        remaining = stream.cap - stream.retained
        if remaining > 0:
            retained = content[:remaining]
            write_all(stream.output, retained)
            stream.retained += len(retained)
        if stream.total > stream.cap:
            return "stream-cap"


def drain_ready(
    selector: selectors.BaseSelector,
    streams: dict[int, StreamState],
    timeout: float = POLL_INTERVAL_SECONDS,
) -> str | None:
    cap_failure = None
    for key, _ in selector.select(timeout):
        if key.data not in ("stdout-cap", "stderr-cap"):
            continue
        stream = streams[key.fd]
        result = drain_stream(stream)
        if stream.eof:
            selector.unregister(stream.descriptor)
            close_descriptor(stream.descriptor)
        if result is not None and cap_failure is None:
            cap_failure = key.data
    return cap_failure


def send_group_signal(state: SupervisionState, selected_signal: signal.Signals) -> None:
    try:
        os.killpg(state.pid, selected_signal)
        if selected_signal == signal.SIGTERM:
            state.term_sent = True
        else:
            state.kill_sent = True
    except ProcessLookupError:
        return
    except OSError as error:
        state.record_error(f"signal-group-{selected_signal.name.lower()}-{error.errno}")


def send_identity_signal(
    state: SupervisionState,
    identity: ProcessIdentity,
    selected_signal: signal.Signals,
) -> None:
    try:
        if not identity_exists(identity):
            return
        os.kill(identity.pid, selected_signal)
        if selected_signal == signal.SIGTERM:
            state.term_sent = True
            state.term_signaled.add(identity)
        else:
            state.kill_sent = True
    except ProcessLookupError:
        return
    except BaseException as error:
        state.record_error(f"signal-child-{selected_signal.name.lower()}-{type(error).__name__}")


def cleanup_iteration(
    state: SupervisionState,
    selector: selectors.BaseSelector,
    streams: dict[int, StreamState],
    selected_signal: signal.Signals,
) -> None:
    try:
        current = observe_descendants(state)
    except BaseException as error:
        state.record_error(f"observe-{type(error).__name__}")
        current = set()
    try:
        send_group_signal(state, selected_signal)
    except BaseException as error:
        state.record_error(f"signal-group-{type(error).__name__}")
    identities = set(state.observed_descendants)
    identities.update(current)
    for identity in sorted(identities):
        if selected_signal == signal.SIGTERM and identity in state.term_signaled:
            continue
        send_identity_signal(state, identity, selected_signal)
    try:
        drain_ready(selector, streams)
    except BaseException as error:
        state.record_error(f"drain-{type(error).__name__}")
    try:
        reap_available(state)
    except BaseException as error:
        state.record_error(f"reap-{type(error).__name__}")


def cleanup_complete(state: SupervisionState, streams: dict[int, StreamState]) -> bool:
    try:
        absent = descendants_absent(state)
    except BaseException as error:
        state.record_error(f"absence-{type(error).__name__}")
        absent = False
    try:
        group_absent = not group_exists(state.pid)
    except BaseException as error:
        state.record_error(f"group-{type(error).__name__}")
        group_absent = False
    return (
        group_absent
        and absent
        and state.raw_wait_status is not None
        and all(stream.eof for stream in streams.values())
    )


def cleanup_tree(
    state: SupervisionState,
    selector: selectors.BaseSelector,
    streams: dict[int, StreamState],
    term_grace_ms: int,
) -> float:
    term_deadline = monotonic_deadline(term_grace_ms)
    while time.monotonic() < term_deadline:
        cleanup_iteration(state, selector, streams, signal.SIGTERM)
        if cleanup_complete(state, streams):
            return time.monotonic() + PUBLICATION_MARGIN_SECONDS
    cleanup_deadline = time.monotonic() + CLEANUP_CAP_SECONDS
    while time.monotonic() < cleanup_deadline:
        cleanup_iteration(state, selector, streams, signal.SIGKILL)
        if cleanup_complete(state, streams):
            return cleanup_deadline + PUBLICATION_MARGIN_SECONDS
    cleanup_iteration(state, selector, streams, signal.SIGKILL)
    if not cleanup_complete(state, streams):
        state.record_error("cleanup-deadline")
    return cleanup_deadline + PUBLICATION_MARGIN_SECONDS


def normalized_exit(raw_wait_status: int | None) -> tuple[int, int]:
    if raw_wait_status is None:
        return -1, 0
    if os.WIFEXITED(raw_wait_status):
        return os.WEXITSTATUS(raw_wait_status), 0
    if os.WIFSIGNALED(raw_wait_status):
        return -1, os.WTERMSIG(raw_wait_status)
    return -1, 0


def final_absence(state: SupervisionState) -> tuple[bool, bool]:
    try:
        group_absent = not group_exists(state.pid)
    except BaseException as error:
        state.record_error(f"publish-group-{type(error).__name__}")
        group_absent = False
    try:
        no_descendants = descendants_absent(state)
    except BaseException as error:
        state.record_error(f"publish-absence-{type(error).__name__}")
        no_descendants = False
    return group_absent, no_descendants


def publish_status(
    descriptor: int,
    deadline: float,
    outcome: str,
    state: SupervisionState,
    stdout: StreamState,
    stderr: StreamState,
) -> None:
    exit_code, exit_signal = normalized_exit(state.raw_wait_status)
    group_absent, no_descendants = final_absence(state)
    if not group_absent or not no_descendants:
        state.record_error("published-live-process")
    fields = [
        STATUS_MAGIC,
        f"outcome={outcome}",
        f"raw_wait_status={state.raw_wait_status if state.raw_wait_status is not None else -1}",
        f"exit_code={exit_code}",
        f"exit_signal={exit_signal}",
        f"term_sent={int(state.term_sent)}",
        f"kill_sent={int(state.kill_sent)}",
        f"reaped_descendants={state.reaped_descendants}",
        f"observed_descendants={len(state.observed_descendants)}",
        f"group_absent={int(group_absent)}",
        f"descendants_absent={int(no_descendants)}",
        f"stdout_bytes={stdout.retained}",
        f"stderr_bytes={stderr.retained}",
        f"stdout_total={stdout.total}",
        f"stderr_total={stderr.total}",
        f"stdout_eof={int(stdout.eof)}",
        f"stderr_eof={int(stderr.eof)}",
        f"cleanup_error={','.join(state.cleanup_errors)}",
        "",
    ]
    write_all(descriptor, "\n".join(fields).encode("ascii"), deadline)
    os.fsync(descriptor)
    if time.monotonic() >= deadline:
        raise TimeoutError("publication deadline")


def complete_handshake(
    state: SupervisionState,
    selector: selectors.BaseSelector,
    ready_read: int,
    release_write: int,
    deadline: float,
    signal_requested: callable,
) -> str | None:
    ready = False
    while True:
        reap_available(state)
        if signal_requested():
            return "supervisor-signal"
        if time.monotonic() >= deadline:
            return "timeout"
        if state.raw_wait_status is not None:
            return "spawn-failure"
        timeout = min(POLL_INTERVAL_SECONDS, max(0.0, deadline - time.monotonic()))
        for key, mask in selector.select(timeout):
            if key.fd == ready_read and mask & selectors.EVENT_READ:
                try:
                    content = os.read(ready_read, 1)
                except BlockingIOError:
                    continue
                if content != b"R":
                    return "spawn-failure"
                if os.getpgid(state.pid) != state.pid or os.getsid(state.pid) != state.pid:
                    return "spawn-failure"
                ready = True
                selector.unregister(ready_read)
                close_descriptor(ready_read)
                selector.register(release_write, selectors.EVENT_WRITE, "release")
            elif key.fd == release_write and ready and mask & selectors.EVENT_WRITE:
                try:
                    count = os.write(release_write, b"G")
                except BlockingIOError:
                    continue
                if count != 1:
                    return "spawn-failure"
                selector.unregister(release_write)
                close_descriptor(release_write)
                return None


def supervise(arguments: argparse.Namespace) -> int:
    deadline = monotonic_deadline(arguments.timeout_ms)
    descriptors: list[int] = []
    state: SupervisionState | None = None
    selector = selectors.DefaultSelector()
    outcome = "spawn-failure"
    requested_signal: int | None = None
    publication_deadline = deadline + PUBLICATION_MARGIN_SECONDS

    def receive_signal(selected_signal: int, _frame: object) -> None:
        nonlocal requested_signal
        requested_signal = selected_signal

    for selected_signal in (signal.SIGHUP, signal.SIGINT, signal.SIGTERM):
        signal.signal(selected_signal, receive_signal)
    signal.signal(signal.SIGXFSZ, signal.SIG_IGN)

    try:
        stdout_descriptor = create_output(arguments.stdout)
        descriptors.append(stdout_descriptor)
        stderr_descriptor = create_output(arguments.stderr)
        descriptors.append(stderr_descriptor)
        status_descriptor = create_output(arguments.status)
        descriptors.append(status_descriptor)
        stdout = StreamState(-1, stdout_descriptor, arguments.stdout_cap)
        stderr = StreamState(-1, stderr_descriptor, arguments.stderr_cap)

        set_subreaper()
        state, stdout_read, stderr_read, ready_read, release_write = spawn_group(arguments.command)
        stdout.descriptor = stdout_read
        stderr.descriptor = stderr_read
        streams = {stdout_read: stdout, stderr_read: stderr}
        selector.register(stdout_read, selectors.EVENT_READ, "stdout-cap")
        selector.register(stderr_read, selectors.EVENT_READ, "stderr-cap")
        selector.register(ready_read, selectors.EVENT_READ, "ready")

        handshake_failure = complete_handshake(
            state,
            selector,
            ready_read,
            release_write,
            deadline,
            lambda: requested_signal is not None,
        )
        if handshake_failure is not None:
            outcome = handshake_failure
        else:
            while True:
                cap_failure = drain_ready(selector, streams)
                reap_available(state)
                observe_descendants(state)
                if cap_failure is not None:
                    outcome = cap_failure
                    break
                if requested_signal is not None:
                    outcome = "supervisor-signal"
                    break
                if time.monotonic() >= deadline:
                    outcome = "timeout"
                    break
                if state.raw_wait_status is not None:
                    if os.WIFEXITED(state.raw_wait_status) and os.WEXITSTATUS(state.raw_wait_status) == 0:
                        if group_exists(state.pid) or not descendants_absent(state):
                            outcome = "live-descendant"
                            break
                        if stdout.eof and stderr.eof:
                            outcome = "success"
                            break
                    else:
                        outcome = "nonzero-exit"
                        break
    except BaseException as error:
        outcome = "supervisor-error"
        if state is not None:
            state.record_error(f"supervision-{type(error).__name__}")
    finally:
        if state is not None:
            streams = {
                stream.descriptor: stream
                for stream in (stdout, stderr)
                if stream.descriptor >= 0
            }
            if outcome != "success" or not cleanup_complete(state, streams):
                publication_deadline = cleanup_tree(
                    state,
                    selector,
                    streams,
                    arguments.term_grace_ms,
                )
            for stream in (stdout, stderr):
                if stream.descriptor >= 0 and not stream.eof:
                    close_descriptor(stream.descriptor)
                try:
                    os.fsync(stream.output)
                except BaseException as error:
                    state.record_error(f"stream-sync-{type(error).__name__}")
            if state.cleanup_errors:
                outcome = "cleanup-failure"
            try:
                publish_status(
                    status_descriptor,
                    publication_deadline,
                    outcome,
                    state,
                    stdout,
                    stderr,
                )
            except BaseException as error:
                state.record_error(f"status-publish-{type(error).__name__}")
                outcome = "cleanup-failure"
        selector.close()
        close_descriptors(descriptors)

    if outcome == "success":
        return 0
    if outcome == "cleanup-failure":
        print("selected-authority supervisor: cleanup failure", file=sys.stderr)
        return 125
    return 1


def main() -> int:
    arguments = parse_arguments()
    try:
        return supervise(arguments)
    except BaseException as error:
        print(
            f"selected-authority supervisor: {type(error).__name__}",
            file=sys.stderr,
        )
        return 125


if __name__ == "__main__":
    raise SystemExit(main())
