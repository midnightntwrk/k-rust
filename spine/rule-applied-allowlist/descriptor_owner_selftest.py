#!/usr/bin/env python3
"""Bounded process/path adversaries for the R3-G-05L two-path contract."""

from __future__ import annotations

import argparse
import json
import os
import select
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Callable

from descriptor_owner import (
    DescriptorOwnerError,
    ProcessGeneration,
    descriptor_is_open,
    owner_descriptor_path,
    process_generation,
    verify_owner_descriptor,
)


FIXED_OWNER_FD = 198
ACCEPTANCE_ADVERSARIES = (
    "outer-owner-and-supervisor-pidfds",
    "grandchild-stable-owner-path",
    "grandchild-immediate-self-fd-closed",
    "stable-java-scratch-and-immediate-record-same-tree",
    "canonical-rename-and-replacement-resistant",
    "owner-fd-absent-in-supervisor-child-grandchild",
    "owner-exit-path-failure-and-exact-session-reap",
    "injected-owner-generation-replacement-rejected",
    "same-number-owner-fd-rebinding-rejected",
    "release-and-boundary-pre-post-identity",
    "owner-supervisor-lifetime-failure-rejection",
    "secure-first-writer-publication-preserved",
)


def write_json(path: Path, value: dict) -> None:
    path.write_text(json.dumps(value, sort_keys=True) + "\n", encoding="utf-8")


def wait_file(path: Path, timeout: float = 3.0) -> None:
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        if path.is_file():
            return
        time.sleep(0.01)
    raise AssertionError(f"timed out waiting for {path}")


def require_owner_fd_absent(fd: int) -> None:
    if descriptor_is_open(fd) or Path(f"/proc/self/fd/{fd}").exists():
        raise AssertionError("outer descriptor owner FD leaked into a descendant")


def synthetic_grandchild(args: argparse.Namespace) -> int:
    require_owner_fd_absent(args.owner_fd)
    self_path_failed = False
    try:
        os.chdir(f"/proc/self/fd/{args.owner_fd}")
    except OSError:
        self_path_failed = True
    if not self_path_failed:
        raise AssertionError("grandchild resolved the closed immediate descriptor spelling")
    try:
        Path(args.record_path).read_text(encoding="utf-8")
    except OSError:
        record_path_failed = True
    else:
        record_path_failed = False
    if not record_path_failed:
        raise AssertionError("grandchild resolved the closed immediate record spelling")
    scratch = Path(args.scratch_path)
    (scratch / "grandchild-write").write_text("descriptor-bound\n", encoding="utf-8")
    write_json(args.result, {
        "grandchildOwnerFdAbsent": True,
        "grandchildImmediatePathFailed": True,
        "grandchildStablePathSucceeded": True,
        "grandchildImmediateRecordPathFailed": True,
    })
    return 0


def synthetic_child(args: argparse.Namespace) -> int:
    require_owner_fd_absent(args.owner_fd)
    immediate_fd = os.open(
        owner_descriptor_path(args.owner_pid, args.owner_fd),
        os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
    immediate_root = Path(f"/proc/self/fd/{immediate_fd}")
    record_path = immediate_root / "records/synthetic.json"
    scratch_immediate = immediate_root / "java-scratch"
    scratch_stable = owner_descriptor_path(args.owner_pid, args.owner_fd) / "java-scratch"
    try:
        record_path.parent.mkdir()
        scratch_immediate.mkdir()
        record_path.write_text("immediate-record\n", encoding="utf-8")
        immediate_identity = os.stat(immediate_root)
        stable_identity = os.stat(owner_descriptor_path(args.owner_pid, args.owner_fd))
        immediate_scratch_identity = os.stat(scratch_immediate)
        stable_scratch_identity = os.stat(scratch_stable)
        if ((immediate_identity.st_dev, immediate_identity.st_ino)
                != (stable_identity.st_dev, stable_identity.st_ino)
                or (immediate_scratch_identity.st_dev, immediate_scratch_identity.st_ino)
                != (stable_scratch_identity.st_dev, stable_scratch_identity.st_ino)):
            raise AssertionError("stable scratch and immediate record roots differ")
        if (not str(record_path).startswith("/proc/self/fd/")
                or str(record_path).startswith(f"/proc/{args.owner_pid}/fd/")
                or not str(scratch_stable).startswith(f"/proc/{args.owner_pid}/fd/")):
            raise AssertionError("scratch/record descriptor spellings are not exact")
        command = [
            sys.executable, str(Path(__file__).resolve()), "grandchild",
            "--owner-pid", str(args.owner_pid), "--owner-fd", str(args.owner_fd),
            "--scratch-path", str(scratch_stable), "--record-path", str(record_path),
            "--result", str(args.result),
        ]
        result = subprocess.run(command, close_fds=True, timeout=3, check=False)
    finally:
        os.close(immediate_fd)
    if result.returncode == 0:
        value = json.loads(args.result.read_text(encoding="utf-8"))
        value["childOwnerFdAbsent"] = True
        value["stableScratchAndImmediateRecordSameTree"] = True
        value["recordPathImmediateOnly"] = True
        write_json(args.result, value)
    return result.returncode


def synthetic_supervisor(args: argparse.Namespace) -> int:
    require_owner_fd_absent(args.owner_fd)
    identity = process_generation(os.getpid())
    if identity is None:
        raise AssertionError("synthetic supervisor generation is unavailable")
    write_json(args.ready, {
        "pid": os.getpid(), "startTimeTicks": identity.start_time,
        "ownerFdAbsent": True,
    })
    wait_file(args.gate)
    command = [
        sys.executable, str(Path(__file__).resolve()), "child",
        "--owner-pid", str(args.owner_pid), "--owner-fd", str(args.owner_fd),
        "--result", str(args.result),
    ]
    child = subprocess.Popen(command, start_new_session=True, close_fds=True)
    status = child.wait(timeout=4)
    write_json(args.supervisor_result, {
        "supervisorOwnerFdAbsent": True,
        "childSessionReaped": status == 0,
        "childPid": child.pid,
    })
    return status


def ephemeral_owner(args: argparse.Namespace) -> int:
    opened = os.open(
        args.directory, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        if opened != FIXED_OWNER_FD:
            os.dup2(opened, FIXED_OWNER_FD, inheritable=False)
            os.close(opened)
            opened = FIXED_OWNER_FD
        identity = process_generation(os.getpid())
        target = os.fstat(opened)
        if identity is None:
            raise AssertionError("ephemeral descriptor owner generation is unavailable")
        write_json(args.ready, {
            "pid": os.getpid(), "startTimeTicks": identity.start_time,
            "fd": opened, "device": target.st_dev, "inode": target.st_ino,
        })
        wait_file(args.gate, timeout=5)
        return 0
    finally:
        if descriptor_is_open(opened):
            os.close(opened)


def owner_path_target(args: argparse.Namespace) -> int:
    require_owner_fd_absent(args.owner_fd)
    wait_file(args.gate, timeout=5)
    try:
        os.chdir(owner_descriptor_path(args.owner_pid, args.owner_fd))
    except OSError:
        write_json(args.failure_ready, {"ownerQualifiedPathRejectedAfterExit": True})
        while True:
            signal.pause()
    Path(args.marker).write_text("unexpected\n", encoding="utf-8")
    return 0


def checked_synchronous_boundary(
    command: list[str], *, owner_pid: int, owner_start: int, owner_fd: int,
    immediate_fd: int, device: int, inode: int,
    consume: Callable[[subprocess.CompletedProcess[bytes]], None],
    after_command: Callable[[], None] | None = None,
) -> None:
    before = verify_owner_descriptor(
        owner_pid, owner_start, owner_fd, immediate_fd, device, inode)
    result = subprocess.run(command, close_fds=True, capture_output=True, check=False)
    if after_command is not None:
        after_command()
    after = verify_owner_descriptor(
        owner_pid, owner_start, owner_fd, immediate_fd, device, inode)
    if after != before or result.returncode != 0:
        raise DescriptorOwnerError("synchronous nested boundary failed")
    consume(result)


def run_live_path_test(base: Path) -> None:
    canonical = base / "output"
    canonical.mkdir()
    opened = os.open(
        canonical, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW)
    if descriptor_is_open(FIXED_OWNER_FD):
        os.close(opened)
        raise AssertionError("fixed self-test owner FD is unexpectedly occupied")
    if opened != FIXED_OWNER_FD:
        os.dup2(opened, FIXED_OWNER_FD, inheritable=False)
        os.close(opened)
    else:
        os.set_inheritable(opened, False)
    owner = process_generation(os.getpid())
    identity = os.fstat(FIXED_OWNER_FD)
    if owner is None:
        raise AssertionError("live descriptor owner generation is unavailable")
    try:
        first = verify_owner_descriptor(
            os.getpid(), owner.start_time, FIXED_OWNER_FD, FIXED_OWNER_FD,
            identity.st_dev, identity.st_ino)
        held = base / "original-held"
        canonical.rename(held)
        canonical.mkdir()
        ready = base / "supervisor-ready.json"
        gate = base / "supervisor-gate"
        result = base / "grandchild-result.json"
        supervisor_result = base / "supervisor-result.json"
        command = [
            sys.executable, str(Path(__file__).resolve()), "supervisor",
            "--owner-pid", str(os.getpid()), "--owner-fd", str(FIXED_OWNER_FD),
            "--ready", str(ready), "--gate", str(gate), "--result", str(result),
            "--supervisor-result", str(supervisor_result),
        ]
        supervisor = subprocess.Popen(command, close_fds=True)
        outer_pidfd = os.pidfd_open(os.getpid(), 0)
        supervisor_pidfd = -1
        try:
            wait_file(ready)
            ready_value = json.loads(ready.read_text(encoding="utf-8"))
            supervisor_pidfd = os.pidfd_open(supervisor.pid, 0)
            if ready_value["pid"] != supervisor.pid:
                raise AssertionError("synthetic supervisor generation was not bound")
            release = verify_owner_descriptor(
                os.getpid(), owner.start_time, FIXED_OWNER_FD, FIXED_OWNER_FD,
                identity.st_dev, identity.st_ino)
            if release != first:
                raise AssertionError("descriptor identity changed before synthetic release")
            gate.write_text("release\n", encoding="utf-8")
            if supervisor.wait(timeout=5) != 0:
                raise AssertionError("synthetic supervisor/child/grandchild chain failed")
            final = verify_owner_descriptor(
                os.getpid(), owner.start_time, FIXED_OWNER_FD, FIXED_OWNER_FD,
                identity.st_dev, identity.st_ino)
            if final != first:
                raise AssertionError("descriptor identity changed across synthetic boundary")
            nested = json.loads(result.read_text(encoding="utf-8"))
            supervised = json.loads(supervisor_result.read_text(encoding="utf-8"))
            if (not all(nested.values()) or not supervised["supervisorOwnerFdAbsent"]
                    or not supervised["childSessionReaped"]
                    or not (held / "java-scratch/grandchild-write").is_file()
                    or not (held / "records/synthetic.json").is_file()
                    or (canonical / "java-scratch/grandchild-write").exists()
                    or (canonical / "records/synthetic.json").exists()):
                raise AssertionError("owner-qualified grandchild path was redirected or inherited")
        finally:
            if supervisor.poll() is None:
                supervisor.kill()
                supervisor.wait(timeout=3)
            os.close(outer_pidfd)
            if supervisor_pidfd >= 0:
                os.close(supervisor_pidfd)

        consumed: list[bytes] = []
        checked_synchronous_boundary(
            [sys.executable, "-c", "print('provisional')"],
            owner_pid=os.getpid(), owner_start=owner.start_time,
            owner_fd=FIXED_OWNER_FD, immediate_fd=FIXED_OWNER_FD,
            device=identity.st_dev, inode=identity.st_ino,
            consume=lambda completed: consumed.append(completed.stdout))
        if consumed != [b"provisional\n"]:
            raise AssertionError("successful checked boundary did not consume its result")

        replacement = base / "replacement"
        replacement.mkdir()
        os.close(FIXED_OWNER_FD)
        rebound = os.open(replacement, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
        if rebound != FIXED_OWNER_FD:
            os.dup2(rebound, FIXED_OWNER_FD, inheritable=False)
            os.close(rebound)
        else:
            os.set_inheritable(rebound, False)
        try:
            verify_owner_descriptor(
                os.getpid(), owner.start_time, FIXED_OWNER_FD, FIXED_OWNER_FD,
                identity.st_dev, identity.st_ino)
        except DescriptorOwnerError:
            pass
        else:
            raise AssertionError("same-number owner FD rebinding was accepted")
    finally:
        if descriptor_is_open(FIXED_OWNER_FD):
            os.close(FIXED_OWNER_FD)


def run_owner_exit_test(base: Path) -> None:
    output = base / "owner-exit-output"
    output.mkdir()
    owner_ready = base / "owner-exit-ready.json"
    owner_gate = base / "owner-exit-gate"
    owner = subprocess.Popen([
        sys.executable, str(Path(__file__).resolve()), "owner",
        "--directory", str(output), "--ready", str(owner_ready),
        "--gate", str(owner_gate),
    ], close_fds=True)
    wait_file(owner_ready)
    bound = json.loads(owner_ready.read_text(encoding="utf-8"))
    immediate_fd = os.open(output, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
    marker = base / "owner-exit-marker"
    target_gate = base / "owner-exit-target-gate"
    path_failure_ready = base / "owner-exit-path-failure.json"
    target = subprocess.Popen([
        sys.executable, str(Path(__file__).resolve()), "target",
        "--owner-pid", str(bound["pid"]), "--owner-fd", str(bound["fd"]),
        "--gate", str(target_gate), "--marker", str(marker),
        "--failure-ready", str(path_failure_ready),
    ], start_new_session=True, close_fds=True)
    replacement = subprocess.Popen(["sleep", "30"], start_new_session=True)
    owner_pidfd = os.pidfd_open(owner.pid, 0)
    target_pidfd = os.pidfd_open(target.pid, 0)
    try:
        verify_owner_descriptor(
            bound["pid"], bound["startTimeTicks"], bound["fd"], immediate_fd,
            bound["device"], bound["inode"])
        rejected_results: list[bytes] = []
        def terminate_owner() -> None:
            owner.terminate()
            owner.wait(timeout=3)

        try:
            checked_synchronous_boundary(
                [sys.executable, "-c", "print('reject')"],
                owner_pid=bound["pid"], owner_start=bound["startTimeTicks"],
                owner_fd=bound["fd"], immediate_fd=immediate_fd,
                device=bound["device"], inode=bound["inode"],
                consume=lambda completed: rejected_results.append(completed.stdout),
                after_command=terminate_owner)
        except DescriptorOwnerError:
            pass
        else:
            raise AssertionError("owner-death boundary unexpectedly consumed provisional output")
        if rejected_results:
            raise AssertionError("failed post-check consumed a provisional compiler result")
        owner.wait(timeout=3)
        if not select.select([owner_pidfd], [], [], 2)[0]:
            raise AssertionError("pidfd watcher did not observe descriptor owner exit")
        try:
            verify_owner_descriptor(
                bound["pid"], bound["startTimeTicks"], bound["fd"], immediate_fd,
                bound["device"], bound["inode"])
        except DescriptorOwnerError:
            pass
        else:
            raise AssertionError("exited descriptor owner remained trusted")
        injected = ProcessGeneration(bound["startTimeTicks"] + 1, "S")
        try:
            verify_owner_descriptor(
                bound["pid"], bound["startTimeTicks"], bound["fd"], immediate_fd,
                bound["device"], bound["inode"], generation_reader=lambda _pid: injected)
        except DescriptorOwnerError:
            pass
        else:
            raise AssertionError("injected descriptor owner replacement was trusted")
        target_gate.write_text("attempt-owner-path\n", encoding="utf-8")
        wait_file(path_failure_ready)
        path_failure = json.loads(path_failure_ready.read_text(encoding="utf-8"))
        if path_failure != {"ownerQualifiedPathRejectedAfterExit": True}:
            raise AssertionError("owner-qualified path did not fail after owner exit")
        signal.pidfd_send_signal(target_pidfd, signal.SIGKILL)
        target.wait(timeout=3)
        if target.returncode != -signal.SIGKILL or marker.exists() or replacement.poll() is not None:
            raise AssertionError("owner-death watcher did not isolate and reap the exact child session")
    finally:
        for process in (owner, target, replacement):
            if process.poll() is None:
                process.kill()
            process.wait(timeout=3)
        os.close(owner_pidfd)
        os.close(target_pidfd)
        os.close(immediate_fd)


def self_test() -> None:
    if len(ACCEPTANCE_ADVERSARIES) != 12 or len(set(ACCEPTANCE_ADVERSARIES)) != 12:
        raise AssertionError("descriptor acceptance adversary ledger is not exact")
    with tempfile.TemporaryDirectory(prefix="r3-g-05-descriptor-owner-") as directory:
        base = Path(directory)
        run_live_path_test(base)
        run_owner_exit_test(base)
    print("R3-G-05 nested descriptor owner path self-test: pass")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", nargs="?", default="self-test",
                        choices=("self-test", "supervisor", "child", "grandchild",
                                 "owner", "target"))
    parser.add_argument("--owner-pid", type=int)
    parser.add_argument("--owner-fd", type=int)
    parser.add_argument("--ready", type=Path)
    parser.add_argument("--gate", type=Path)
    parser.add_argument("--result", type=Path)
    parser.add_argument("--supervisor-result", type=Path)
    parser.add_argument("--directory", type=Path)
    parser.add_argument("--marker", type=Path)
    parser.add_argument("--failure-ready", type=Path)
    parser.add_argument("--scratch-path")
    parser.add_argument("--record-path")
    args = parser.parse_args()
    if args.mode == "self-test":
        self_test()
    elif args.mode == "supervisor":
        raise SystemExit(synthetic_supervisor(args))
    elif args.mode == "child":
        raise SystemExit(synthetic_child(args))
    elif args.mode == "grandchild":
        raise SystemExit(synthetic_grandchild(args))
    elif args.mode == "owner":
        raise SystemExit(ephemeral_owner(args))
    else:
        raise SystemExit(owner_path_target(args))


if __name__ == "__main__":
    main()
