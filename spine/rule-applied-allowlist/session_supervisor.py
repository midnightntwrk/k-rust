#!/usr/bin/env python3
"""Validated-before-exec owner for one bounded R3-G-05 raw session."""

from __future__ import annotations

import argparse
import ctypes
import hashlib
import json
import os
import select
import signal
import subprocess
import sys
import time
from pathlib import Path

from descriptor_owner import (
    descriptor_is_open,
    verify_owner_descriptor,
)
from resource_watchdog import (
    SessionGeneration,
    bind_process,
    bound_process_identity,
    close_bound,
    identity_record,
    private_receive,
    private_send,
    proc_stat,
    signal_session,
)
from secure_io import (
    durable_unlink,
    ensure_directory,
    publish_outer_session,
    publish_watchdog_done,
    verify_directory,
)


TERM_GRACE_SECONDS = 1.0
EMPTY_WAIT_SECONDS = 5.0
READY_WAIT_SECONDS = 3.0
WATCHDOG_DONE_CONTENT = b"external-empty-session-verification\n"
GATE_PROGRAM = r"""
import os
import select
import sys
import time
release_fd = int(sys.argv[1])
ack_fd = int(sys.argv[2])
fail_ack = sys.argv[3] == "1"
command = sys.argv[4:]
deadline = time.monotonic() + 2.0
token = bytearray()
while len(token) < 65:
    remaining = deadline - time.monotonic()
    if remaining <= 0 or not select.select([release_fd], [], [], remaining)[0]:
        os._exit(126)
    chunk = os.read(release_fd, 65 - len(token))
    if not chunk:
        os._exit(126)
    token.extend(chunk)
remaining = deadline - time.monotonic()
if remaining <= 0 or not select.select([release_fd], [], [], remaining)[0]:
    os._exit(126)
if os.read(release_fd, 1) != b"":
    os._exit(126)
os.close(release_fd)
if token[:1] != b"R" or len(token) != 65:
    os._exit(126)
if fail_ack:
    os.close(ack_fd)
    os._exit(127)
ack = b"T" + bytes(token[1:])
if os.write(ack_fd, ack) != len(ack):
    os._exit(127)
os.close(ack_fd)
os.execvpe(command[0], command, os.environ)
"""


def become_subreaper() -> None:
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(36, 1, 0, 0, 0) != 0:  # PR_SET_CHILD_SUBREAPER
        raise OSError(ctypes.get_errno(), "PR_SET_CHILD_SUBREAPER failed")


def reap_session_children(tracker: SessionGeneration,
                          *, exclude: set[int] | None = None) -> set[int]:
    reaped: set[int] = set()
    excluded = exclude or set()
    for process in tracker.select_members():
        try:
            if process.pid in excluded or bound_process_identity(process) is None:
                continue
            waited = os.waitid(os.P_PIDFD, process.pidfd, os.WEXITED | os.WNOHANG)
            if waited is not None:
                reaped.add(process.pid)
        except (ChildProcessError, ProcessLookupError):
            pass
        finally:
            close_bound(process)
    return reaped


def member_snapshot(tracker: SessionGeneration) -> tuple[set[int], set[int]]:
    """Take one generation-bound, zombie-inclusive member/process-group snapshot."""
    pids: set[int] = set()
    groups: set[int] = set()
    for process in tracker.select_members():
        try:
            value = bound_process_identity(process)
            if value is not None:
                pids.add(process.pid)
                groups.add(value.process_group)
        finally:
            close_bound(process)
    return pids, groups


def wait_empty(tracker: SessionGeneration, deadline: float, *,
               leader: subprocess.Popen[bytes] | None = None,
               reaped: set[int] | None = None) -> bool:
    excluded = {leader.pid} if leader is not None else set()
    while time.monotonic() < deadline:
        if leader is not None:
            leader.poll()
        found = reap_session_children(tracker, exclude=excluded)
        if reaped is not None:
            reaped.update(found)
        if not tracker.current_members():
            return True
        time.sleep(0.02)
    if leader is not None:
        leader.poll()
    found = reap_session_children(tracker, exclude=excluded)
    if reaped is not None:
        reaped.update(found)
    return not tracker.current_members()


def terminate_whole_session(tracker: SessionGeneration, *,
                            leader: subprocess.Popen[bytes] | None = None,
                            reaped: set[int] | None = None) -> bool:
    """Signal only pidfd-bound members of the original session generation."""
    signal_session(
        tracker.session,
        tracker.select_members(),
        signal.SIGTERM,
    )
    if wait_empty(tracker, time.monotonic() + TERM_GRACE_SECONDS,
                  leader=leader, reaped=reaped):
        return True
    signal_session(
        tracker.session,
        tracker.select_members(),
        signal.SIGKILL,
    )
    return wait_empty(tracker, time.monotonic() + EMPTY_WAIT_SECONDS,
                      leader=leader, reaped=reaped)


def _load_ready(path: Path) -> dict:
    if not path.is_file() or path.is_symlink():
        raise RuntimeError("watchdog readiness is not a regular record")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise RuntimeError(f"watchdog readiness is malformed: {error}") from error
    if not isinstance(value, dict):
        raise RuntimeError("watchdog readiness is not an object")
    return value


def wait_for_readiness(path: Path, private_fd: int,
                       watchdog: subprocess.Popen[bytes], *, target_pid: int,
                       target_start: int, owner_pid: int,
                       owner_start: int, descriptor_owner_pid: int,
                       descriptor_owner_start: int, descriptor_owner_fd: int,
                       output_fd: int, output_device: int,
                       output_inode: int) -> tuple[dict, str, dict]:
    private = private_receive(
        private_fd, deadline=time.monotonic() + READY_WAIT_SECONDS)
    value = _load_ready(path)
    target = proc_stat(target_pid)
    owner = proc_stat(owner_pid)
    descriptor_owner = proc_stat(descriptor_owner_pid)
    watchdog_identity = proc_stat(watchdog.pid)
    descriptor_proof = verify_owner_descriptor(
        descriptor_owner_pid, descriptor_owner_start, descriptor_owner_fd,
        output_fd, output_device, output_inode)
    expected = {
        "schema": "R3-G-05-watchdog-ready-v1",
        "target": None if target is None else identity_record(target_pid, target),
        "owner": None if owner is None else identity_record(owner_pid, owner),
        "descriptorOwner": (None if descriptor_owner is None else
                            identity_record(descriptor_owner_pid, descriptor_owner)),
        "outputDescriptor": {
            "fd": descriptor_owner_fd,
            "device": descriptor_proof.device,
            "inode": descriptor_proof.inode,
            "ownerPath": str(descriptor_proof.owner_path),
        },
        "watchdog": (None if watchdog_identity is None
                     else identity_record(watchdog.pid, watchdog_identity)),
        "pidfdGenerationBound": True,
    }
    if (target is None or target.start_time != target_start
            or target.session != target_pid or target.process_group != target_pid
            or owner is None or owner.start_time != owner_start
            or descriptor_owner is None
            or descriptor_owner.start_time != descriptor_owner_start
            or watchdog_identity is None or watchdog_identity.state in ("T", "t", "Z")
            or watchdog.poll() is not None
            or value != expected):
        raise RuntimeError("watchdog readiness generation binding mismatch")
    handles = []
    try:
        handles.append(bind_process(
            target_pid, expected_session=target_pid, expected_group=target_pid,
            expected_start=target_start))
        handles.append(bind_process(owner_pid, expected_start=owner_start))
        handles.append(bind_process(
            descriptor_owner_pid, expected_start=descriptor_owner_start))
        handles.append(bind_process(
            watchdog.pid, expected_start=watchdog_identity.start_time))
    finally:
        for handle in handles:
            close_bound(handle)
    readiness_sha = hashlib.sha256(path.read_bytes()).hexdigest()
    expected_private = {
        "type": "watchdog-readiness",
        "readinessSha256": readiness_sha,
        "target": expected["target"],
        "owner": expected["owner"],
        "descriptorOwner": expected["descriptorOwner"],
        "outputDescriptor": expected["outputDescriptor"],
        "watchdog": expected["watchdog"],
    }
    if private != expected_private:
        raise RuntimeError("private watchdog readiness digest mismatch")
    return value, readiness_sha, expected_private


def _target_acknowledgement(fd: int, readiness_sha: str) -> None:
    deadline = time.monotonic() + 2.0
    expected = b"T" + readiness_sha.encode("ascii")
    received = bytearray()
    try:
        while len(received) < len(expected):
            remaining = deadline - time.monotonic()
            if remaining <= 0 or not select.select([fd], [], [], remaining)[0]:
                raise RuntimeError("target gate acknowledgement timed out")
            chunk = os.read(fd, len(expected) - len(received))
            if not chunk:
                raise RuntimeError("target gate acknowledgement ended early")
            received.extend(chunk)
        remaining = deadline - time.monotonic()
        if remaining <= 0 or not select.select([fd], [], [], remaining)[0]:
            raise RuntimeError("target gate acknowledgement writer did not close")
        if os.read(fd, 1) != b"" or bytes(received) != expected:
            raise RuntimeError("target gate acknowledgement binding mismatch")
    finally:
        os.close(fd)


def approve_watchdog(approval_fd: int, release_ack_fd: int, target_ack_fd: int,
                     readiness: dict, readiness_sha: str,
                     watchdog: subprocess.Popen[bytes], *, corrupt: bool = False) -> None:
    approval = {**readiness, "type": "supervisor-approval"}
    if corrupt:
        approval["readinessSha256"] = "0" * 64
    unclaimed = [approval_fd, release_ack_fd, target_ack_fd]
    try:
        unclaimed.pop(0)
        private_send(approval_fd, approval)
        unclaimed.pop(0)
        acknowledgement = private_receive(release_ack_fd)
        if acknowledgement != {
                **readiness, "type": "watchdog-release-acknowledgement"}:
            raise RuntimeError("watchdog release acknowledgement binding mismatch")
        identity = proc_stat(watchdog.pid)
        if (identity is None or identity.state in ("T", "t", "Z")
                or watchdog.poll() is not None
                or identity.start_time != readiness["watchdog"]["startTimeTicks"]):
            raise RuntimeError("watchdog stopped or exited during private gate release")
        unclaimed.pop(0)
        _target_acknowledgement(target_ack_fd, readiness_sha)
    finally:
        for fd in unclaimed:
            os.close(fd)


def dispose_watchdog(watchdog: subprocess.Popen[bytes], records: Path,
                     *, allow_disarm: bool) -> tuple[int, bool, str, str | None]:
    """Make one final decision, reap once, and return the exact final status."""
    done = records / "watchdog.done"
    if allow_disarm and watchdog.poll() is None:
        publish_watchdog_done(records, WATCHDOG_DONE_CONTENT)
        try:
            status = watchdog.wait(timeout=3)
        except subprocess.TimeoutExpired:
            watchdog.kill()
            status = watchdog.wait(timeout=2)
        if status == 0:
            return (status, True, "disarmed-after-successful-empty",
                    hashlib.sha256(done.read_bytes()).hexdigest())
        durable_unlink(done, missing_ok=True)
        return status, False, "armed-failure-after-disarm-attempt", None

    if done.exists() or done.is_symlink():
        raise RuntimeError("armed failure refuses an unowned watchdog done marker")
    already_exited = watchdog.poll() is not None
    if not already_exited:
        watchdog.kill()
    status = watchdog.wait(timeout=2)
    if status == 0:
        raise RuntimeError("armed watchdog produced an impossible zero failure status")
    disposition = ("armed-failure-exited" if already_exited
                   else "armed-failure-terminated")
    return status, False, disposition, None


def launch(args: argparse.Namespace) -> int:
    become_subreaper()
    if descriptor_is_open(args.descriptor_owner_fd):
        raise RuntimeError("outer descriptor owner FD leaked into the supervisor")
    output_fd = verify_directory(args.output, args.output_device, args.output_inode)
    if output_fd == args.descriptor_owner_fd:
        os.close(output_fd)
        raise RuntimeError("immediate output FD collided with the excluded owner FD")
    os.set_inheritable(output_fd, True)
    descriptor_proof = verify_owner_descriptor(
        args.descriptor_owner_pid, args.descriptor_owner_start_time,
        args.descriptor_owner_fd, output_fd, args.output_device, args.output_inode)
    secure_output = Path(f"/proc/self/fd/{output_fd}")
    records = secure_output / "records"
    ensure_directory(records)
    ready_path = records / "watchdog.ready.json"
    watchdog_record = records / "watchdog.json"
    watchdog_done = records / "watchdog.done"
    supervisor_record = secure_output / "outer-session.json"
    environment = {
        **os.environ,
        "R3_G_05_OUTPUT_FD": str(output_fd),
        "R3_G_05_DESCRIPTOR_OWNER_PID": str(args.descriptor_owner_pid),
        "R3_G_05_DESCRIPTOR_OWNER_START_TIME": str(args.descriptor_owner_start_time),
        "R3_G_05_DESCRIPTOR_OWNER_FD": str(args.descriptor_owner_fd),
        "R3_G_05_OUTPUT_DEVICE": str(args.output_device),
        "R3_G_05_OUTPUT_INODE": str(args.output_inode),
    }
    child: subprocess.Popen[bytes] | None = None
    watchdog: subprocess.Popen[bytes] | None = None
    tracker: SessionGeneration | None = None
    gate_read, gate_write = os.pipe()
    target_ack_read, target_ack_write = os.pipe()
    private_ready_read, private_ready_write = os.pipe()
    approval_read, approval_write = os.pipe()
    release_ack_read, release_ack_write = os.pipe()
    owned_fds = {
        gate_read, gate_write, target_ack_read, target_ack_write,
        private_ready_read, private_ready_write, approval_read, approval_write,
        release_ack_read, release_ack_write,
    }

    def close_owned(fd: int) -> None:
        if fd in owned_fds:
            os.close(fd)
            owned_fds.remove(fd)
    target_session = -1
    target_start = -1
    owner_identity = proc_stat(os.getpid())
    if owner_identity is None:
        raise RuntimeError("launcher process identity is unavailable")
    observed_groups: set[int] = set()
    reason = "launcher-failure"
    inner_status = 125
    empty = False
    readiness_validated = False
    readiness_sha: str | None = None
    gate_released = False
    watchdog_result: tuple[int, bool, str, str | None] | None = None
    reaped_children: set[int] = set()
    exit_time_descendants: set[int] = set()
    interrupted = 0

    def handle_signal(signum: int, _frame: object) -> None:
        nonlocal interrupted
        interrupted = signum

    previous_handlers = {}
    for signum in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
        previous_handlers[signum] = signal.signal(signum, handle_signal)

    def final_record(watchdog_status: int, disarmed: bool, disposition: str,
                     done_sha: str | None) -> dict:
        return {
            "schema": "R3-G-05-outer-session-v1",
            "sessionId": target_session,
            "sessionStartTimeTicks": target_start,
            "outputDevice": args.output_device,
            "outputInode": args.output_inode,
            "innerStatus": inner_status,
            "reason": reason,
            "targetSessionEmpty": empty,
            "watchdogStatus": watchdog_status,
            "watchdogDisarmedAfterEmpty": disarmed,
            "watchdogDoneSha256": done_sha,
            "watchdogDisposition": disposition,
            "watchdogReadinessValidated": readiness_validated,
            "privateWatchdogReadinessValidated": readiness_validated,
            "watchdogReadySha256": readiness_sha,
            "rawCommandReleased": gate_released,
            "watchdogOnlyGateReleaseAcknowledged": gate_released,
            "targetGateReleaseAcknowledged": gate_released,
            "doubleBracketedSessionSelection": True,
            "nonInferentialExitClassification": True,
            "ownerPid": os.getpid(),
            "ownerStartTimeTicks": owner_identity.start_time,
            "descriptorOwnerPid": args.descriptor_owner_pid,
            "descriptorOwnerStartTimeTicks": args.descriptor_owner_start_time,
            "descriptorOwnerFd": args.descriptor_owner_fd,
            "descriptorOwnerPath": str(descriptor_proof.owner_path),
            "descriptorOwnerGenerationValidated": True,
            "descriptorOwnerFdExcludedFromTarget": True,
            "nestedBoundaryPrePostChecks": True,
            "provisionalResultsRejectedOnPostcheckFailure": True,
            "observedProcessGroupCount": len(observed_groups),
            "reapedSessionChildCount": len(reaped_children),
            "reapedSessionChildPids": sorted(reaped_children),
            "exitTimeDescendantPids": sorted(exit_time_descendants),
            "wallTimeoutSeconds": args.timeout,
        }

    started = time.monotonic()
    try:
        child = subprocess.Popen(
            [sys.executable, "-c", GATE_PROGRAM,
             str(gate_read), str(target_ack_write),
             "1" if args.test_target_ack_failure else "0", *args.command],
            env=environment,
            start_new_session=True,
            pass_fds=(output_fd, gate_read, target_ack_write),
        )
        close_owned(gate_read)
        close_owned(target_ack_write)
        identity = proc_stat(child.pid)
        if (identity is None or identity.session != child.pid
                or identity.process_group != child.pid):
            raise RuntimeError("raw gate did not become its owned session leader")
        target_session = child.pid
        target_start = identity.start_time
        tracker = SessionGeneration(target_session, target_start)
        if Path(f"/proc/{child.pid}/fd/{args.descriptor_owner_fd}").exists():
            raise RuntimeError("outer descriptor owner FD leaked into the target gate")
        watchdog_command = [
            sys.executable, str(args.watchdog),
            "--session", str(target_session), "--pgid", str(target_session),
            "--leader", str(child.pid), "--leader-start-time", str(target_start),
            "--record", str(watchdog_record), "--ready-file", str(ready_path),
            "--done-file", str(watchdog_done), "--owner-pid", str(os.getpid()),
            "--owner-start-time", str(owner_identity.start_time),
            "--descriptor-owner-pid", str(args.descriptor_owner_pid),
            "--descriptor-owner-start-time", str(args.descriptor_owner_start_time),
            "--descriptor-owner-fd", str(args.descriptor_owner_fd),
            "--output-fd", str(output_fd),
            "--output-device", str(args.output_device),
            "--output-inode", str(args.output_inode),
            "--interval", "0.05",
        ]
        if args.test_watchdog_exit_before_ready:
            watchdog_command.append("--test-exit-before-ready")
        if args.test_readiness_corruption:
            watchdog_command.append("--test-corrupt-ready")
        if args.test_watchdog_pressure:
            watchdog_command.append("--test-pressure")
        if args.test_private_ready_eof:
            watchdog_command.append("--test-private-ready-eof")
        if args.test_watchdog_stop_after_ready:
            watchdog_command.append("--test-stop-after-ready")
        if args.test_watchdog_kill_after_ready:
            watchdog_command.append("--test-kill-after-ready")
        if args.test_watchdog_kill_after_approval:
            watchdog_command.append("--test-kill-after-approval")
        if args.test_gate_release_failure:
            watchdog_command.append("--test-gate-release-failure")
        watchdog_command.extend([
            "--private-ready-fd", str(private_ready_write),
            "--approval-fd", str(approval_read),
            "--gate-write-fd", str(gate_write),
            "--release-ack-fd", str(release_ack_write),
        ])
        if args.test_public_ready_precreation:
            ready_path.write_bytes(b"attacker-first-writer\n")
        watchdog = subprocess.Popen(
            watchdog_command, start_new_session=True,
            pass_fds=(output_fd, private_ready_write, approval_read,
                      gate_write, release_ack_write))
        for fd in (private_ready_write, approval_read, gate_write, release_ack_write):
            close_owned(fd)
        owned_fds.remove(private_ready_read)
        _ready, readiness_sha, private_readiness = wait_for_readiness(
            ready_path, private_ready_read, watchdog,
            target_pid=child.pid, target_start=target_start,
            owner_pid=os.getpid(), owner_start=owner_identity.start_time,
            descriptor_owner_pid=args.descriptor_owner_pid,
            descriptor_owner_start=args.descriptor_owner_start_time,
            descriptor_owner_fd=args.descriptor_owner_fd,
            output_fd=output_fd, output_device=args.output_device,
            output_inode=args.output_inode,
        )
        readiness_validated = True
        if args.test_launcher_failure:
            raise RuntimeError("injected launcher failure")
        for fd in (approval_write, release_ack_read, target_ack_read):
            owned_fds.remove(fd)
        # This is the final owner-generation and descriptor identity proof
        # immediately before the watchdog alone releases the raw command.
        release_proof = verify_owner_descriptor(
            args.descriptor_owner_pid, args.descriptor_owner_start_time,
            args.descriptor_owner_fd, output_fd, args.output_device, args.output_inode)
        if release_proof != descriptor_proof:
            raise RuntimeError("descriptor owner identity changed before raw release")
        approve_watchdog(
            approval_write, release_ack_read, target_ack_read,
            private_readiness, readiness_sha, watchdog,
            corrupt=args.test_private_approval_corruption)
        gate_released = True
        deadline = started + args.timeout
        while True:
            child_status = child.poll()
            if child_status is None:
                reaped_now = reap_session_children(tracker, exclude={child.pid})
                reaped_children.update(reaped_now)
                _members, groups = member_snapshot(tracker)
                observed_groups.update(groups)
            else:
                post_exit_members, groups = member_snapshot(tracker)
                observed_groups.update(groups)
                exit_time_descendants.update(
                    pid for pid in post_exit_members if pid != child.pid)
                reaped_now = reap_session_children(tracker, exclude={child.pid})
                reaped_children.update(reaped_now)
            watchdog_poll = watchdog.poll()
            if interrupted:
                reason = f"launcher-signal-{interrupted}"
                inner_status = 128 + interrupted
                break
            if (args.test_watchdog_crash and time.monotonic() - started >= 0.20
                    and watchdog_poll is None):
                watchdog.kill()
                watchdog_poll = watchdog.wait(timeout=2)
            if watchdog_poll is not None:
                reason = "watchdog-failure"
                inner_status = watchdog_poll if watchdog_poll > 0 else 76
                break
            if time.monotonic() >= deadline:
                reason = "wall-timeout"
                inner_status = 124
                break
            if child_status is not None:
                watchdog_fired = False
                if watchdog_record.is_file() and not watchdog_record.is_symlink():
                    try:
                        watchdog_fired = json.loads(
                            watchdog_record.read_text(encoding="utf-8")
                        ).get("fired") is True
                    except (OSError, json.JSONDecodeError):
                        pass
                if watchdog_fired:
                    time.sleep(0.02)
                    continue
                inner_status = child_status if child_status >= 0 else 128 - child_status
                if exit_time_descendants:
                    reason = "descendants-survived-inner-exit"
                    if inner_status == 0:
                        inner_status = 72
                else:
                    reason = "inner-success" if inner_status == 0 else "inner-failure"
                break
            time.sleep(0.02)

        if reason != "inner-success" or tracker.current_members():
            empty = terminate_whole_session(
                tracker, leader=child, reaped=reaped_children)
        else:
            empty = True
        if child.poll() is None:
            try:
                child.wait(timeout=EMPTY_WAIT_SECONDS)
            except subprocess.TimeoutExpired:
                empty = terminate_whole_session(
                    tracker, leader=child, reaped=reaped_children) and empty
                child.wait(timeout=EMPTY_WAIT_SECONDS)
        if not wait_empty(tracker, time.monotonic() + EMPTY_WAIT_SECONDS,
                          leader=child, reaped=reaped_children):
            empty = False
        if not empty:
            reason = "session-termination-unproven"
            inner_status = 73
        successful_empty = (
            readiness_validated and gate_released and inner_status == 0
            and reason == "inner-success" and empty
        )
        watchdog_result = dispose_watchdog(
            watchdog, records, allow_disarm=successful_empty)
        watchdog_status, disarmed, disposition, done_sha = watchdog_result
        if inner_status == 0 and not disarmed:
            inner_status, reason = 75, "watchdog-terminal-failure"
        try:
            publish_outer_session(
                secure_output,
                final_record(watchdog_status, disarmed, disposition, done_sha),
            )
        except BaseException:
            if disarmed:
                durable_unlink(watchdog_done)
                inner_status, reason = 125, "outer-session-publication-failure"
                watchdog_result = (
                    watchdog_status, False,
                    "armed-failure-terminal-publication-rollback", None)
            raise
        return inner_status
    except BaseException:
        if tracker is not None:
            empty = terminate_whole_session(
                tracker, leader=child, reaped=reaped_children)
        if child is not None and child.poll() is None:
            try:
                child.wait(timeout=EMPTY_WAIT_SECONDS)
            except subprocess.TimeoutExpired:
                pass
        if watchdog is not None:
            if watchdog_result is None:
                watchdog_result = dispose_watchdog(
                    watchdog, records, allow_disarm=False)
            watchdog_status, disarmed, disposition, done_sha = watchdog_result
            try:
                publish_outer_session(
                    secure_output,
                    final_record(watchdog_status, disarmed, disposition, done_sha),
                )
            except BaseException:
                pass
        raise
    finally:
        for fd in tuple(owned_fds):
            close_owned(fd)
        os.close(output_fd)
        for signum, handler in previous_handlers.items():
            signal.signal(signum, handler)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--output-device", required=True, type=int)
    parser.add_argument("--output-inode", required=True, type=int)
    parser.add_argument("--descriptor-owner-pid", required=True, type=int)
    parser.add_argument("--descriptor-owner-start-time", required=True, type=int)
    parser.add_argument("--descriptor-owner-fd", required=True, type=int)
    parser.add_argument("--watchdog", required=True, type=Path)
    parser.add_argument("--timeout", required=True, type=int)
    parser.add_argument("--test-watchdog-crash", action="store_true")
    parser.add_argument("--test-launcher-failure", action="store_true")
    parser.add_argument("--test-readiness-corruption", action="store_true")
    parser.add_argument("--test-watchdog-exit-before-ready", action="store_true")
    parser.add_argument("--test-gate-release-failure", action="store_true")
    parser.add_argument("--test-public-ready-precreation", action="store_true")
    parser.add_argument("--test-private-ready-eof", action="store_true")
    parser.add_argument("--test-watchdog-stop-after-ready", action="store_true")
    parser.add_argument("--test-watchdog-kill-after-ready", action="store_true")
    parser.add_argument("--test-watchdog-kill-after-approval", action="store_true")
    parser.add_argument("--test-target-ack-failure", action="store_true")
    parser.add_argument("--test-private-approval-corruption", action="store_true")
    parser.add_argument("--test-watchdog-pressure", action="store_true")
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if args.command[:1] == ["--"]:
        args.command = args.command[1:]
    if not args.command:
        parser.error("a raw-inner command is required")
    try:
        status = launch(args)
    except BaseException as error:
        print(f"R3-G-05 session supervisor failed: {error}", file=sys.stderr)
        status = 125
    raise SystemExit(status)


if __name__ == "__main__":
    main()
