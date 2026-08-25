#!/usr/bin/env python3
"""Watch one exact process generation and its complete Linux session."""

from __future__ import annotations

import argparse
import errno
import hashlib
import json
import os
import select
import signal
import struct
import subprocess
import tempfile
import threading
import time
from pathlib import Path
from typing import Callable, Iterable, NamedTuple

from descriptor_owner import verify_owner_descriptor
from secure_io import publish_watchdog_ready, replace_progress_json


class ProcessIdentity(NamedTuple):
    session: int
    process_group: int
    rss_kib: int
    start_time: int
    state: str


class BoundProcess(NamedTuple):
    pid: int
    session: int
    process_group: int
    start_time: int
    pidfd: int


ProcReader = Callable[[int], ProcessIdentity | None]
FRAME_LIMIT = 4096
PRIVATE_IO_SECONDS = 2.0


def proc_stat(pid: int) -> ProcessIdentity | None:
    try:
        raw = Path(f"/proc/{pid}/stat").read_text(encoding="ascii")
        fields = raw[raw.rfind(")") + 2:].split()
        return ProcessIdentity(
            session=int(fields[3]),
            process_group=int(fields[2]),
            rss_kib=int(fields[21]) * os.sysconf("SC_PAGE_SIZE") // 1024,
            start_time=int(fields[19]),
            state=fields[0],
        )
    except (FileNotFoundError, PermissionError, IndexError, ValueError, ProcessLookupError):
        return None


def private_send(fd: int, value: dict, *, deadline: float | None = None) -> None:
    """Send one bounded canonical private frame, then revoke this write end."""
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("ascii")
    if len(encoded) > FRAME_LIMIT:
        raise RuntimeError("private frame exceeds its bound")
    packet = struct.pack("!I", len(encoded)) + encoded
    limit = deadline if deadline is not None else time.monotonic() + PRIVATE_IO_SECONDS
    try:
        while packet:
            remaining = limit - time.monotonic()
            if remaining <= 0 or not select.select([], [fd], [], remaining)[1]:
                raise RuntimeError("private frame write timed out")
            written = os.write(fd, packet)
            if written <= 0:
                raise RuntimeError("private frame write was incomplete")
            packet = packet[written:]
    finally:
        os.close(fd)


def _private_read_exact(fd: int, size: int, deadline: float) -> bytes:
    value = bytearray()
    while len(value) < size:
        remaining = deadline - time.monotonic()
        if remaining <= 0 or not select.select([fd], [], [], remaining)[0]:
            raise RuntimeError("private frame read timed out")
        chunk = os.read(fd, size - len(value))
        if not chunk:
            raise RuntimeError("private frame ended before completion")
        value.extend(chunk)
    return bytes(value)


def private_receive(fd: int, *, deadline: float | None = None) -> dict:
    """Receive exactly one bounded canonical frame and require writer revocation."""
    limit = deadline if deadline is not None else time.monotonic() + PRIVATE_IO_SECONDS
    try:
        length = struct.unpack("!I", _private_read_exact(fd, 4, limit))[0]
        if length <= 0 or length > FRAME_LIMIT:
            raise RuntimeError("private frame length is invalid")
        encoded = _private_read_exact(fd, length, limit)
        remaining = limit - time.monotonic()
        if remaining <= 0 or not select.select([fd], [], [], remaining)[0]:
            raise RuntimeError("private frame writer did not close")
        if os.read(fd, 1) != b"":
            raise RuntimeError("private channel contains an extra frame or bytes")
        try:
            value = json.loads(encoded.decode("ascii"))
        except (UnicodeDecodeError, json.JSONDecodeError) as error:
            raise RuntimeError("private frame is malformed") from error
        if (not isinstance(value, dict)
                or json.dumps(value, sort_keys=True, separators=(",", ":")).encode("ascii")
                != encoded):
            raise RuntimeError("private frame is not canonical")
        return value
    finally:
        os.close(fd)


def identity_record(pid: int, identity: ProcessIdentity) -> dict[str, int]:
    return {
        "pid": pid,
        "sessionId": identity.session,
        "processGroupId": identity.process_group,
        "startTimeTicks": identity.start_time,
    }


def process_alive(pid: int, start_time: int | None = None,
                  *, reader: ProcReader = proc_stat) -> bool:
    value = reader(pid)
    return (value is not None and value.state not in ("Z", "T", "t")
            and (start_time is None or value.start_time == start_time))


def _pidfd_pid(pidfd: int) -> int:
    for line in Path(f"/proc/self/fdinfo/{pidfd}").read_text(encoding="ascii").splitlines():
        if line.startswith("Pid:"):
            return int(line.split(":", 1)[1])
    raise RuntimeError("pidfd lacks a kernel PID binding")


def bind_process(pid: int, *, expected_session: int | None = None,
                 expected_group: int | None = None,
                 expected_start: int | None = None,
                 reader: ProcReader = proc_stat, allow_zombie: bool = False) -> BoundProcess:
    """Open a pidfd before validation and bind every checked identity field."""
    pidfd = os.pidfd_open(pid, 0)
    try:
        if _pidfd_pid(pidfd) != pid:
            raise RuntimeError("pidfd PID binding mismatch")
        value = reader(pid)
        if value is None or (value.state == "Z" and not allow_zombie):
            raise ProcessLookupError(pid)
        if expected_session is not None and value.session != expected_session:
            raise RuntimeError("process session identity mismatch")
        if expected_group is not None and value.process_group != expected_group:
            raise RuntimeError("process group identity mismatch")
        if expected_start is not None and value.start_time != expected_start:
            raise RuntimeError("process generation identity mismatch")
        if value.state != "Z":
            signal.pidfd_send_signal(pidfd, 0)
        return BoundProcess(pid, value.session, value.process_group,
                            value.start_time, pidfd)
    except BaseException:
        os.close(pidfd)
        raise


def close_bound(process: BoundProcess | None) -> None:
    if process is not None:
        try:
            os.close(process.pidfd)
        except OSError:
            pass


def _bound_process_sample_current(
        process: BoundProcess, value: ProcessIdentity | None, *,
        allow_zombie: bool = False) -> bool:
    """Validate one proc sample against the bound pidfd generation."""
    if (value is None or (value.state == "Z" and not allow_zombie)
            or value.start_time != process.start_time
            or value.session != process.session or value.process_group != process.process_group):
        return False
    try:
        signal.pidfd_send_signal(process.pidfd, 0)
        return True
    except OSError as error:
        if error.errno in (errno.ESRCH, errno.EBADF):
            return False
        raise


def bound_process_generation_current(
        process: BoundProcess, *, reader: ProcReader = proc_stat,
        allow_zombie: bool = False) -> bool:
    """Check the exact pidfd generation; stopped generations remain current."""
    return _bound_process_sample_current(
        process, reader(process.pid), allow_zombie=allow_zombie)


def bound_process_alive(process: BoundProcess, *, reader: ProcReader = proc_stat) -> bool:
    """Require an operational generation for readiness/owner progress."""
    value = reader(process.pid)
    return (value is not None and value.state not in ("Z", "T", "t")
            and _bound_process_sample_current(process, value))


def owner_generation_alive(owner: BoundProcess, *, reader: ProcReader = proc_stat) -> bool:
    """Owner liveness means the exact launcher generation, never its numeric PID."""
    return bound_process_alive(owner, reader=reader)


def bound_process_identity(process: BoundProcess, *, reader: ProcReader = proc_stat,
                           allow_zombie: bool = True) -> ProcessIdentity | None:
    value = reader(process.pid)
    if (value is None or (value.state == "Z" and not allow_zombie)
            or value.start_time != process.start_time or value.session != process.session
            or value.process_group != process.process_group):
        return None
    return value


def signal_bound_process(process: BoundProcess, signum: signal.Signals,
                         *, reader: ProcReader = proc_stat) -> bool:
    """Signal only the generation selected by pidfd; identity change is stale."""
    if not bound_process_generation_current(process, reader=reader):
        return False
    try:
        signal.pidfd_send_signal(process.pidfd, signum)
        return True
    except ProcessLookupError:
        return False


def proc_pids() -> list[int]:
    return sorted(int(entry.name) for entry in Path("/proc").iterdir()
                  if entry.name.isdigit())


class SessionSelection(NamedTuple):
    processes: list[BoundProcess]
    stale: bool


def _leader_bracket(session: int, start_time: int, reader: ProcReader) -> bool:
    value = reader(session)
    return (value is None or (value.start_time == start_time
            and value.session == session and value.process_group == session))


def select_session_generation(
        session: int, session_start_time: int, *, reader: ProcReader = proc_stat,
        enumerate_pids: Callable[[], Iterable[int]] = proc_pids,
        opener: Callable[[int, int], int] = os.pidfd_open,
        pidfd_pid: Callable[[int], int] = _pidfd_pid,
        closer: Callable[[int], None] = os.close) -> SessionSelection:
    """Double-bracket enumeration and return only fully generation-bound handles."""
    if not _leader_bracket(session, session_start_time, reader):
        return SessionSelection([], True)
    selected: list[BoundProcess] = []
    try:
        for pid in sorted(set(enumerate_pids())):
            observed = reader(pid)
            if observed is None or observed.session != session:
                continue
            try:
                pidfd = opener(pid, 0)
            except (ProcessLookupError, PermissionError):
                continue
            keep = False
            try:
                rebound = reader(pid)
                if (pidfd_pid(pidfd) == pid and rebound is not None
                        and rebound.start_time == observed.start_time
                        and rebound.session == observed.session
                        and rebound.process_group == observed.process_group):
                    selected.append(BoundProcess(
                        pid, rebound.session, rebound.process_group,
                        rebound.start_time, pidfd))
                    keep = True
            finally:
                if not keep:
                    closer(pidfd)
        if not _leader_bracket(session, session_start_time, reader):
            for process in selected:
                closer(process.pidfd)
            return SessionSelection([], True)
        return SessionSelection(selected, False)
    except BaseException:
        for process in selected:
            closer(process.pidfd)
        raise


def session_members(session: int, session_start_time: int | None = None,
                    *, reader: ProcReader = proc_stat) -> list[int]:
    """Return zombie-inclusive members, generation-bound whenever a start is known."""
    if session_start_time is None:
        return sorted(pid for pid in proc_pids()
                      if (value := reader(pid)) is not None and value.session == session)
    selection = select_session_generation(session, session_start_time, reader=reader)
    try:
        return [process.pid for process in selection.processes]
    finally:
        for process in selection.processes:
            close_bound(process)


class SessionGeneration:
    """Latch completion so a later reuse of the numeric SID stays unrelated."""

    def __init__(self, session: int, start_time: int,
                 *, selector: Callable[[int, int], SessionSelection] =
                 select_session_generation) -> None:
        self.session = session
        self.start_time = start_time
        self.completed = False
        self._selector = selector

    def select_members(self) -> list[BoundProcess]:
        if self.completed:
            return []
        selection = self._selector(self.session, self.start_time)
        if selection.stale or not selection.processes:
            self.completed = True
        return selection.processes

    def current_members(self) -> list[int]:
        if self.completed:
            return []
        selected = self.select_members()
        try:
            return [process.pid for process in selected]
        finally:
            for process in selected:
                close_bound(process)


def bind_session_members(session: int, session_start_time: int) -> list[BoundProcess]:
    return select_session_generation(session, session_start_time).processes


def signal_session(session: int, selected: list[BoundProcess],
                   signum: signal.Signals) -> None:
    for process in selected:
        try:
            if process.session == session:
                signal_bound_process(process, signum)
        finally:
            close_bound(process)


def session_rss_kib(tracker: SessionGeneration) -> int:
    total = 0
    for process in tracker.select_members():
        try:
            value = bound_process_identity(process)
            if value is not None:
                total += value.rss_kib
        finally:
            close_bound(process)
    return total


def memory() -> tuple[int, int]:
    values = {}
    for line in Path("/proc/meminfo").read_text(encoding="ascii").splitlines():
        key, value, *_ = line.replace(":", "").split()
        values[key] = int(value)
    return values["MemAvailable"], values["SwapFree"]


def write_record(path: Path, record: dict) -> None:
    replace_progress_json(path, record)


def wait_session_empty(tracker: SessionGeneration, deadline: float) -> bool:
    while time.monotonic() < deadline:
        if not tracker.current_members():
            return True
        time.sleep(0.02)
    return not tracker.current_members()


def terminate_session(tracker: SessionGeneration) -> bool:
    signal_session(tracker.session, tracker.select_members(), signal.SIGTERM)
    if wait_session_empty(tracker, time.monotonic() + 1.0):
        return True
    signal_session(tracker.session, tracker.select_members(), signal.SIGKILL)
    return wait_session_empty(tracker, time.monotonic() + 5.0)


def _release_gate(fd: int, readiness_sha: str) -> None:
    packet = b"R" + readiness_sha.encode("ascii")
    deadline = time.monotonic() + PRIVATE_IO_SECONDS
    try:
        while packet:
            remaining = deadline - time.monotonic()
            if remaining <= 0 or not select.select([], [fd], [], remaining)[1]:
                raise RuntimeError("watchdog gate release timed out")
            written = os.write(fd, packet)
            if written <= 0:
                raise RuntimeError("watchdog gate release was incomplete")
            packet = packet[written:]
    finally:
        os.close(fd)


def _close_quietly(fd: int) -> None:
    try:
        os.close(fd)
    except OSError:
        pass


def watch(args: argparse.Namespace) -> int:
    leader_handle: BoundProcess | None = None
    owner_handle: BoundProcess | None = None
    descriptor_owner_handle: BoundProcess | None = None
    try:
        if args.test_exit_before_ready:
            return 78
        leader_handle = bind_process(
            args.leader, expected_session=args.session, expected_group=args.pgid,
            expected_start=args.leader_start_time,
        )
        owner_handle = bind_process(args.owner_pid, expected_start=args.owner_start_time)
        descriptor_owner_handle = bind_process(
            args.descriptor_owner_pid,
            expected_start=args.descriptor_owner_start_time)
        descriptor_proof = verify_owner_descriptor(
            args.descriptor_owner_pid, args.descriptor_owner_start_time,
            args.descriptor_owner_fd, args.output_fd,
            args.output_device, args.output_inode)
        watchdog_identity = proc_stat(os.getpid())
        owner_identity = proc_stat(args.owner_pid)
        descriptor_owner_identity = proc_stat(args.descriptor_owner_pid)
        leader_identity = proc_stat(args.leader)
        if (watchdog_identity is None or owner_identity is None
                or descriptor_owner_identity is None or leader_identity is None
                or args.session != args.pgid or args.leader != args.session):
            raise SystemExit("watchdog target/owner generation identity mismatch")
        ready = {
            "schema": "R3-G-05-watchdog-ready-v1",
            "target": identity_record(args.leader, leader_identity),
            "owner": identity_record(args.owner_pid, owner_identity),
            "descriptorOwner": identity_record(
                args.descriptor_owner_pid, descriptor_owner_identity),
            "outputDescriptor": {
                "fd": args.descriptor_owner_fd,
                "device": descriptor_proof.device,
                "inode": descriptor_proof.inode,
                "ownerPath": str(descriptor_proof.owner_path),
            },
            "watchdog": identity_record(os.getpid(), watchdog_identity),
            "pidfdGenerationBound": True,
        }
        if args.test_corrupt_ready:
            ready["target"]["startTimeTicks"] += 1
        publish_watchdog_ready(args.ready_file.parent, ready)
        readiness_sha = hashlib.sha256(args.ready_file.read_bytes()).hexdigest()
        private_ready = {
            "type": "watchdog-readiness",
            "readinessSha256": readiness_sha,
            "target": ready["target"],
            "owner": ready["owner"],
            "descriptorOwner": ready["descriptorOwner"],
            "outputDescriptor": ready["outputDescriptor"],
            "watchdog": ready["watchdog"],
        }
        if args.test_stop_after_ready:
            os.kill(os.getpid(), signal.SIGSTOP)
        if args.test_kill_after_ready:
            os.kill(os.getpid(), signal.SIGKILL)
        if args.test_private_ready_eof:
            os.close(args.private_ready_fd)
            args.private_ready_fd = -1
            return 79
        private_send(args.private_ready_fd, private_ready)
        args.private_ready_fd = -1
        approval = private_receive(args.approval_fd)
        args.approval_fd = -1
        current_watchdog = proc_stat(os.getpid())
        if (approval != {**private_ready, "type": "supervisor-approval"}
                or not bound_process_alive(leader_handle)
                or not owner_generation_alive(owner_handle)
                or not owner_generation_alive(descriptor_owner_handle)
                or current_watchdog is None or current_watchdog.state in ("T", "t", "Z")
                or current_watchdog.start_time != watchdog_identity.start_time
                or hashlib.sha256(args.ready_file.read_bytes()).hexdigest() != readiness_sha):
            raise RuntimeError("private watchdog approval binding mismatch")
        if args.test_kill_after_approval:
            os.kill(os.getpid(), signal.SIGKILL)
        if args.test_gate_release_failure:
            os.close(args.gate_write_fd)
            args.gate_write_fd = -1
            raise RuntimeError("injected watchdog-only gate release failure")
        _release_gate(args.gate_write_fd, readiness_sha)
        args.gate_write_fd = -1
        private_send(args.release_ack_fd, {
            **private_ready,
            "type": "watchdog-release-acknowledgement",
        })
        args.release_ack_fd = -1
        tracker = SessionGeneration(args.session, args.leader_start_time)
        peak = 0
        fired = False
        reason = ""
        record = {
            "schema": "R3-G-05-session-watchdog-v1",
            "sessionId": args.session,
            "sessionStartTimeTicks": args.leader_start_time,
            "processGroupId": args.pgid,
            "rssLimitMiB": args.rss_limit_mib,
            "availableMemoryFloorMiB": args.available_floor_mib,
            "swapFreeFloorMiB": args.swap_floor_mib,
            "pollIntervalSeconds": args.interval,
            "peakSessionRssKiB": 0,
            "fired": False,
            "reason": "",
            "completed": False,
            "ownerPid": args.owner_pid,
            "ownerStartTimeTicks": args.owner_start_time,
            "descriptorOwnerPid": args.descriptor_owner_pid,
            "descriptorOwnerStartTimeTicks": args.descriptor_owner_start_time,
            "descriptorOwnerFd": args.descriptor_owner_fd,
            "descriptorOwnerPath": str(descriptor_proof.owner_path),
            "descriptorOwnerPidfdGenerationBound": True,
            "launcherOwnerPidfdGenerationBound": True,
            "descriptorOwnerBindingsRetainedThroughTeardown": True,
            "watchdogPid": os.getpid(),
            "watchdogStartTimeTicks": watchdog_identity.start_time,
            "readinessPublished": True,
            "privateReadinessAuthenticated": True,
            "supervisorApprovalValidated": True,
            "watchdogOnlyGateRelease": True,
            "pidfdGenerationBound": True,
        }
        armed_at = time.monotonic()
        while not args.done_file.is_file() or args.done_file.is_symlink():
            rss = session_rss_kib(tracker)
            available, swap_free = memory()
            peak = max(peak, rss)
            if args.test_pressure and time.monotonic() - armed_at >= 0.10:
                fired, reason = True, "injected-resource-pressure"
            elif not owner_generation_alive(owner_handle):
                fired, reason = True, "launcher-owner-failure"
            elif not owner_generation_alive(descriptor_owner_handle):
                fired, reason = True, "descriptor-owner-failure"
            elif rss > args.rss_limit_mib * 1024:
                fired, reason = True, "session-rss-limit"
            elif available < args.available_floor_mib * 1024:
                fired, reason = True, "available-memory-floor"
            elif swap_free < args.swap_floor_mib * 1024:
                fired, reason = True, "swap-free-floor"
            record.update(peakSessionRssKiB=peak, fired=fired, reason=reason)
            write_record(args.record, record)
            if fired:
                if args.test_pressure:
                    # Exercise final-status capture when the armed watchdog
                    # exits while authoritative launcher teardown is pending.
                    signal_session(
                        tracker.session,
                        tracker.select_members(),
                        signal.SIGTERM,
                    )
                    terminated = False
                else:
                    terminated = terminate_session(tracker)
                record.update(completed=False, sessionTerminationProven=terminated)
                write_record(args.record, record)
                return 70
            time.sleep(args.interval)
        empty = not tracker.current_members()
        record.update(peakSessionRssKiB=peak, fired=False, reason="",
                      completed=empty, sessionTerminationProven=empty)
        write_record(args.record, record)
        return 0 if empty else 71
    finally:
        for name in ("private_ready_fd", "approval_fd", "gate_write_fd", "release_ack_fd"):
            fd = getattr(args, name, -1)
            if fd >= 0:
                _close_quietly(fd)
                setattr(args, name, -1)
        close_bound(leader_handle)
        close_bound(owner_handle)
        close_bound(descriptor_owner_handle)


def self_test() -> None:
    for payload in (b"", struct.pack("!I", 1) + b"{",
                    struct.pack("!I", 2) + b"{}" + b"extra"):
        frame_read, frame_write = os.pipe()
        if payload:
            os.write(frame_write, payload)
        os.close(frame_write)
        try:
            private_receive(frame_read)
        except RuntimeError:
            pass
        else:
            raise AssertionError("malformed/EOF/extra private frame was accepted")
    with tempfile.TemporaryDirectory(prefix="r3-g-05-watchdog-test-") as directory:
        base = Path(directory)
        record = base / "watchdog.json"
        unrelated = subprocess.Popen(["sleep", "30"], start_new_session=True)
        target = subprocess.Popen(
            ["bash", "-c", "set -m; sleep 30 & sleep 30 & wait"], start_new_session=True,
            stderr=subprocess.DEVNULL,
        )
        time.sleep(0.1)
        target_identity = proc_stat(target.pid)
        owner_identity = proc_stat(os.getpid())
        assert target_identity is not None and owner_identity is not None
        target_groups = {
            value.process_group for pid in session_members(target.pid, target_identity.start_time)
            if (value := proc_stat(pid)) is not None
        }
        if len(target_groups) < 2:
            raise AssertionError("synthetic watchdog tree did not create multiple process groups")
        output_fd = os.open(base, os.O_RDONLY | os.O_DIRECTORY)
        try:
            private_ready_read, private_ready_write = os.pipe()
            approval_read, approval_write = os.pipe()
            gate_read, gate_write = os.pipe()
            release_ack_read, release_ack_write = os.pipe()
            protocol_errors: list[BaseException] = []

            def protocol_supervisor() -> None:
                try:
                    readiness = private_receive(private_ready_read)
                    private_send(approval_write, {
                        **readiness, "type": "supervisor-approval"})
                    acknowledgement = private_receive(release_ack_read)
                    assert acknowledgement == {
                        **readiness, "type": "watchdog-release-acknowledgement"}
                    token = bytearray()
                    while True:
                        chunk = os.read(gate_read, 65 - len(token) if len(token) < 65 else 1)
                        if not chunk:
                            break
                        token.extend(chunk)
                    os.close(gate_read)
                    assert bytes(token) == b"R" + readiness["readinessSha256"].encode()
                except BaseException as error:
                    protocol_errors.append(error)

            protocol_thread = threading.Thread(target=protocol_supervisor)
            protocol_thread.start()
            args = argparse.Namespace(
                session=target.pid, pgid=target.pid, leader=target.pid,
                leader_start_time=target_identity.start_time,
                record=record, ready_file=base / "watchdog.ready.json",
                rss_limit_mib=0, available_floor_mib=0,
                swap_floor_mib=0, interval=0.05, done_file=base / "done",
                owner_pid=os.getpid(), owner_start_time=owner_identity.start_time,
                descriptor_owner_pid=os.getpid(),
                descriptor_owner_start_time=owner_identity.start_time,
                descriptor_owner_fd=output_fd,
                output_fd=output_fd, output_device=base.stat().st_dev,
                output_inode=base.stat().st_ino,
                test_exit_before_ready=False, test_corrupt_ready=False,
                test_pressure=False,
                private_ready_fd=private_ready_write, approval_fd=approval_read,
                gate_write_fd=gate_write, release_ack_fd=release_ack_write,
                test_private_ready_eof=False, test_stop_after_ready=False,
                test_kill_after_ready=False, test_kill_after_approval=False,
                test_gate_release_failure=False,
            )
            assert watch(args) == 70
            protocol_thread.join(timeout=3)
            assert not protocol_thread.is_alive() and not protocol_errors
            target.wait(timeout=5)
            assert unrelated.poll() is None
            result = json.loads(record.read_text(encoding="utf-8"))
            assert result["fired"] is True and result["reason"] == "session-rss-limit"

            # Inject a selection-to-signal PID replacement.  The pidfd-bound
            # original and the unrelated replacement must both remain unchanged.
            probe = subprocess.Popen(["sleep", "30"], start_new_session=True)
            replacement = subprocess.Popen(["sleep", "30"], start_new_session=True)
            real = proc_stat(probe.pid)
            other = proc_stat(replacement.pid)
            assert real is not None and other is not None
            after_final = select_session_generation(
                probe.pid, real.start_time, enumerate_pids=lambda: [probe.pid])
            assert not after_final.stale and len(after_final.processes) == 1
            handle = after_final.processes[0]
            stopped = ProcessIdentity(real.session, real.process_group, real.rss_kib,
                                      real.start_time, "T")
            assert bound_process_generation_current(
                handle, reader=lambda _pid: stopped)
            assert not bound_process_alive(handle, reader=lambda _pid: stopped)
            assert signal_bound_process(
                handle, 0, reader=lambda _pid: stopped)
            samples = iter((real, stopped))
            assert bound_process_alive(handle, reader=lambda _pid: next(samples))
            assert next(samples).state == "T"
            changed = ProcessIdentity(real.session, real.process_group, real.rss_kib,
                                      real.start_time + 1, real.state)
            assert not signal_bound_process(
                handle, signal.SIGTERM,
                reader=lambda pid: changed if pid == probe.pid else proc_stat(pid))
            assert probe.poll() is None and replacement.poll() is None
            # The same injected generation change models launcher PID reuse:
            # owner-death detection rejects the replacement rather than accepting it.
            assert not owner_generation_alive(handle, reader=lambda _pid: changed)
            assert probe.poll() is None and replacement.poll() is None
            close_bound(handle)
            probe.terminate()
            replacement.terminate()
            probe.wait(timeout=3)
            replacement.wait(timeout=3)

            # Deterministic bracket adversaries cover SID replacement before
            # enumeration, during enumeration, and candidate replacement while
            # pidfd binding. No replacement/unrelated sentinel is ever selected.
            original = ProcessIdentity(41, 41, 1, 100, "S")
            reused = ProcessIdentity(41, 41, 1, 101, "S")
            unrelated_identity = ProcessIdentity(77, 77, 1, 700, "S")
            sentinels = {41: reused, 52: unrelated_identity}
            before = select_session_generation(
                41, 100, reader=lambda pid: sentinels.get(pid),
                enumerate_pids=lambda: [41, 52], opener=lambda pid, _flags: pid + 1000,
                pidfd_pid=lambda fd: fd - 1000, closer=lambda _fd: None)
            assert before.stale and before.processes == [] and sentinels[52] == unrelated_identity

            during_state = {41: original, 52: unrelated_identity}
            def during_enumeration() -> list[int]:
                during_state[41] = reused
                return [41, 52]
            during = select_session_generation(
                41, 100, reader=lambda pid: during_state.get(pid),
                enumerate_pids=during_enumeration, opener=lambda pid, _flags: pid + 1000,
                pidfd_pid=lambda fd: fd - 1000, closer=lambda _fd: None)
            assert during.stale and during.processes == []
            assert during_state[52] == unrelated_identity

            binding_reads = {41: 0, 51: 0}
            candidate_original = ProcessIdentity(41, 51, 1, 500, "S")
            candidate_reused = ProcessIdentity(41, 51, 1, 501, "S")
            def binding_reader(pid: int) -> ProcessIdentity | None:
                binding_reads[pid] = binding_reads.get(pid, 0) + 1
                if pid == 41:
                    return original
                if pid == 51:
                    return candidate_original if binding_reads[pid] == 1 else candidate_reused
                return None
            closed_fake: list[int] = []
            binding = select_session_generation(
                41, 100, reader=binding_reader, enumerate_pids=lambda: [51],
                opener=lambda pid, _flags: pid + 1000,
                pidfd_pid=lambda fd: fd - 1000, closer=closed_fake.append)
            assert not binding.stale and binding.processes == [] and closed_fake == [1051]

            # Post-empty SID reuse is latched as completed and never rescanned.
            calls = iter((SessionSelection([], False),
                          SessionSelection([handle], False)))
            tracker = SessionGeneration(target.pid, target_identity.start_time,
                                        selector=lambda _sid, _start: next(calls))
            assert tracker.current_members() == []
            assert tracker.current_members() == []
        finally:
            os.close(output_fd)
            if target.poll() is None:
                os.killpg(os.getpgid(target.pid), signal.SIGKILL)
            if unrelated.poll() is None:
                os.killpg(os.getpgid(unrelated.pid), signal.SIGKILL)
            target.wait(timeout=5)
            unrelated.wait(timeout=5)
    print("R3-G-05 watchdog generation-safe process-tree self-test: pass")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--session", type=int)
    parser.add_argument("--pgid", type=int)
    parser.add_argument("--leader", type=int)
    parser.add_argument("--leader-start-time", type=int)
    parser.add_argument("--record", type=Path)
    parser.add_argument("--ready-file", type=Path)
    parser.add_argument("--done-file", type=Path)
    parser.add_argument("--owner-pid", type=int)
    parser.add_argument("--owner-start-time", type=int)
    parser.add_argument("--descriptor-owner-pid", type=int)
    parser.add_argument("--descriptor-owner-start-time", type=int)
    parser.add_argument("--descriptor-owner-fd", type=int)
    parser.add_argument("--output-fd", type=int)
    parser.add_argument("--output-device", type=int)
    parser.add_argument("--output-inode", type=int)
    parser.add_argument("--private-ready-fd", type=int)
    parser.add_argument("--approval-fd", type=int)
    parser.add_argument("--gate-write-fd", type=int)
    parser.add_argument("--release-ack-fd", type=int)
    parser.add_argument("--rss-limit-mib", type=int, default=6144)
    parser.add_argument("--available-floor-mib", type=int, default=4096)
    parser.add_argument("--swap-floor-mib", type=int, default=1024)
    parser.add_argument("--interval", type=float, default=1.0)
    parser.add_argument("--test-exit-before-ready", action="store_true")
    parser.add_argument("--test-corrupt-ready", action="store_true")
    parser.add_argument("--test-pressure", action="store_true")
    parser.add_argument("--test-private-ready-eof", action="store_true")
    parser.add_argument("--test-stop-after-ready", action="store_true")
    parser.add_argument("--test-kill-after-ready", action="store_true")
    parser.add_argument("--test-kill-after-approval", action="store_true")
    parser.add_argument("--test-gate-release-failure", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    required = (args.session, args.pgid, args.leader, args.leader_start_time,
                args.record, args.ready_file, args.done_file,
                args.owner_pid, args.owner_start_time, args.private_ready_fd,
                args.descriptor_owner_pid, args.descriptor_owner_start_time,
                args.descriptor_owner_fd, args.output_fd, args.output_device,
                args.output_inode, args.approval_fd, args.gate_write_fd,
                args.release_ack_fd)
    if None in required:
        parser.error("target, owner, readiness, record, and done identities are required")
    raise SystemExit(watch(args))


if __name__ == "__main__":
    main()
