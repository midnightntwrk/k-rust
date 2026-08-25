#!/usr/bin/env python3
"""Zero-backend whole-session launcher and teardown adversaries."""

from __future__ import annotations

import fcntl
import os
import json
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path

from cache_integrity import complete_outer
from resource_watchdog import proc_stat, process_alive, session_members
from secure_io import publish_raw_failure


DESCRIPTOR_OWNER_FDS: list[int] = []


def command(task: Path, output: Path, timeout: int, child: list[str],
            *, crash_watchdog: bool = False,
            launcher_failure: bool = False,
            readiness_corruption: bool = False,
            watchdog_exit_before_ready: bool = False,
            gate_release_failure: bool = False,
            watchdog_pressure: bool = False,
            public_ready_precreation: bool = False,
            private_ready_eof: bool = False,
            watchdog_stop_after_ready: bool = False,
            watchdog_kill_after_ready: bool = False,
            watchdog_kill_after_approval: bool = False,
            target_ack_failure: bool = False,
            private_approval_corruption: bool = False) -> list[str]:
    identity = output.stat()
    owner_identity = proc_stat(os.getpid())
    if owner_identity is None:
        raise AssertionError("launcher self-test descriptor owner is unavailable")
    opened = os.open(
        output, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW)
    owner_fd = fcntl.fcntl(opened, fcntl.F_DUPFD_CLOEXEC, 198)
    os.close(opened)
    DESCRIPTOR_OWNER_FDS.append(owner_fd)
    value = [
        sys.executable, str(task / "session_supervisor.py"),
        "--output", str(output), "--output-device", str(identity.st_dev),
        "--output-inode", str(identity.st_ino), "--watchdog",
        str(task / "resource_watchdog.py"), "--timeout", str(timeout),
        "--descriptor-owner-pid", str(os.getpid()),
        "--descriptor-owner-start-time", str(owner_identity.start_time),
        "--descriptor-owner-fd", str(owner_fd),
    ]
    if crash_watchdog:
        value.append("--test-watchdog-crash")
    if launcher_failure:
        value.append("--test-launcher-failure")
    if readiness_corruption:
        value.append("--test-readiness-corruption")
    if watchdog_exit_before_ready:
        value.append("--test-watchdog-exit-before-ready")
    if gate_release_failure:
        value.append("--test-gate-release-failure")
    if watchdog_pressure:
        value.append("--test-watchdog-pressure")
    if public_ready_precreation:
        value.append("--test-public-ready-precreation")
    if private_ready_eof:
        value.append("--test-private-ready-eof")
    if watchdog_stop_after_ready:
        value.append("--test-watchdog-stop-after-ready")
    if watchdog_kill_after_ready:
        value.append("--test-watchdog-kill-after-ready")
    if watchdog_kill_after_approval:
        value.append("--test-watchdog-kill-after-approval")
    if target_ack_failure:
        value.append("--test-target-ack-failure")
    if private_approval_corruption:
        value.append("--test-private-approval-corruption")
    return [*value, "--", *child]


def record(output: Path) -> dict:
    return json.loads((output / "outer-session.json").read_text(encoding="utf-8"))


def require_watchdog_shape(output: Path, value: dict, *, successful: bool) -> None:
    done = output / "records/watchdog.done"
    if successful:
        if (value["watchdogStatus"] != 0
                or value["watchdogDisarmedAfterEmpty"] is not True
                or value["watchdogDoneSha256"] is None
                or value["watchdogDisposition"] != "disarmed-after-successful-empty"
                or value["watchdogReadinessValidated"] is not True
                or value["privateWatchdogReadinessValidated"] is not True
                or value["rawCommandReleased"] is not True
                or value["watchdogOnlyGateReleaseAcknowledged"] is not True
                or value["targetGateReleaseAcknowledged"] is not True
                or value["doubleBracketedSessionSelection"] is not True
                or value["nonInferentialExitClassification"] is not True
                or value["descriptorOwnerGenerationValidated"] is not True
                or value["descriptorOwnerFdExcludedFromTarget"] is not True
                or value["nestedBoundaryPrePostChecks"] is not True
                or value["provisionalResultsRejectedOnPostcheckFailure"] is not True
                or value["watchdogReadySha256"] is None
                or not (output / "records/watchdog.ready.json").is_file()
                or not done.is_file()):
            raise AssertionError(f"successful watchdog disarm shape is invalid: {value}")
    elif (value["watchdogStatus"] in (None, 0)
          or value["watchdogDisarmedAfterEmpty"] is not False
          or value["watchdogDoneSha256"] is not None
          or not value["watchdogDisposition"].startswith("armed-failure-")
          or done.exists() or done.is_symlink()):
        raise AssertionError(f"failure received success-shaped watchdog provenance: {value}")


def run_immediate_success_stress(task: Path, directory: Path) -> None:
    for index in range(20):
        output = directory / f"immediate-success-{index:02d}"
        output.mkdir()
        result = subprocess.run(
            command(task, output, 5, ["true"]), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=8, check=False,
        )
        value = record(output)
        if (result.returncode != 0 or value["reason"] != "inner-success"
                or not value["targetSessionEmpty"] or session_members(value["sessionId"])):
            raise AssertionError(f"immediate success iteration {index} failed: {value}")
        require_watchdog_shape(output, value, successful=True)


def run_preexecution_refusal_cases(task: Path, directory: Path) -> None:
    cases = (
        ("readiness-corruption", {"readiness_corruption": True}, False),
        ("watchdog-exit-before-ready", {"watchdog_exit_before_ready": True}, False),
        ("public-readiness-precreation", {"public_ready_precreation": True}, False),
        ("private-readiness-eof", {"private_ready_eof": True}, False),
        ("watchdog-stop-after-ready", {"watchdog_stop_after_ready": True}, False),
        ("watchdog-kill-after-ready", {"watchdog_kill_after_ready": True}, False),
        ("watchdog-kill-after-approval", {"watchdog_kill_after_approval": True}, True),
        ("gate-release-failure", {"gate_release_failure": True}, True),
        ("target-ack-failure", {"target_ack_failure": True}, True),
        ("private-approval-corruption", {"private_approval_corruption": True}, True),
    )
    for name, flags, ready_expected in cases:
        output = directory / name
        output.mkdir()
        payload_marker = directory / f"{name}.payload-ran"
        source = "import pathlib,sys; pathlib.Path(sys.argv[1]).write_text('ran')"
        result = subprocess.run(
            command(task, output, 5,
                    [sys.executable, "-c", source, str(payload_marker)], **flags),
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=8, check=False,
        )
        value = record(output)
        if (result.returncode != 125 or payload_marker.exists()
                or value["rawCommandReleased"] is not False
                or value["watchdogReadinessValidated"] is not ready_expected
                or not value["targetSessionEmpty"]):
            raise AssertionError(f"{name} did not fail closed before raw execution: {value}")
        require_watchdog_shape(output, value, successful=False)


def run_wait_case(task: Path, directory: Path, name: str, expected_status: int) -> None:
    output = directory / name
    output.mkdir()
    started = time.monotonic()
    result = subprocess.run(command(task, output, 5, [
        "bash", "-c",
        "sleep 0.25; printf 'synthetic-launcher-stdout\\n'; "
        "printf 'synthetic-launcher-stderr\\n' >&2; exit \"$1\"",
        "_", str(expected_status),
    ]), text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=10, check=False)
    elapsed = time.monotonic() - started
    if result.returncode != expected_status or elapsed < 0.20:
        raise AssertionError(f"synthetic {name} did not synchronously propagate status")
    if "synthetic-launcher-stdout\n" not in result.stdout:
        raise AssertionError(f"synthetic {name} stdout lifetime was not preserved")
    if "synthetic-launcher-stderr\n" not in result.stderr:
        raise AssertionError(f"synthetic {name} stderr lifetime was not preserved")
    value = record(output)
    if value["innerStatus"] != expected_status or not value["targetSessionEmpty"]:
        raise AssertionError(f"synthetic {name} lacks empty-session proof")
    require_watchdog_shape(output, value, successful=expected_status == 0)


def run_tree_case(task: Path, directory: Path, name: str, *, watchdog_crash: bool) -> None:
    output = directory / name
    output.mkdir()
    unrelated = subprocess.Popen(["sleep", "30"], start_new_session=True)
    try:
        result = subprocess.run(command(task, output, 5 if watchdog_crash else 1, [
            "bash", "-c",
            "set -m; (trap '' TERM; while :; do sleep 1; done) & "
            "(while :; do sleep 1; done) & wait",
        ], crash_watchdog=watchdog_crash), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=10, check=False)
        value = record(output)
        expected_reason = "watchdog-failure" if watchdog_crash else "wall-timeout"
        if (result.returncode == 0 or value["reason"] != expected_reason
                or value["observedProcessGroupCount"] < 2
                or not value["targetSessionEmpty"]
                or session_members(value["sessionId"])):
            raise AssertionError(f"{name} did not terminate/prove its whole multi-pgrp session: {value}")
        require_watchdog_shape(output, value, successful=False)
        if unrelated.poll() is not None:
            raise AssertionError(f"{name} touched an unrelated session")
    finally:
        if unrelated.poll() is None:
            os.killpg(os.getpgid(unrelated.pid), signal.SIGKILL)
        unrelated.wait(timeout=5)


def run_launcher_failure_case(task: Path, directory: Path) -> None:
    output = directory / "injected-launcher-failure"
    output.mkdir()
    unrelated = subprocess.Popen(["sleep", "30"], start_new_session=True)
    try:
        result = subprocess.run(command(task, output, 5, [
            "bash", "-c", "while :; do sleep 1; done",
        ], launcher_failure=True), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=10, check=False)
        value = record(output)
        if (result.returncode != 125 or value["reason"] != "launcher-failure"
                or value["innerStatus"] != 125 or not value["targetSessionEmpty"]):
            raise AssertionError(f"injected launcher failure provenance is invalid: {value}")
        require_watchdog_shape(output, value, successful=False)
        if unrelated.poll() is not None:
            raise AssertionError("injected launcher failure touched an unrelated session")
    finally:
        if unrelated.poll() is None:
            os.killpg(os.getpgid(unrelated.pid), signal.SIGKILL)
        unrelated.wait(timeout=5)


def run_adopted_zombie_case(task: Path, directory: Path) -> None:
    output = directory / "adopted-zombie"
    output.mkdir()
    descendant_pid_path = directory / "adopted-zombie.pid"
    unrelated = subprocess.Popen(["sleep", "30"], start_new_session=True)
    source = """
import os
import pathlib
import time

pid_path = pathlib.Path(os.environ["R3_G_05_TEST_DESCENDANT_PID"])
leader = os.getpid()
descendant = os.fork()
if descendant == 0:
    pid_path.write_text(str(os.getpid()), encoding="ascii")
    deadline = time.monotonic() + 3
    while pathlib.Path(f"/proc/{leader}").exists():
        if time.monotonic() >= deadline:
            os._exit(92)
        time.sleep(0.005)
    os._exit(0)
deadline = time.monotonic() + 3
while not pid_path.is_file():
    if time.monotonic() >= deadline:
        os._exit(91)
    try:
        pid_path.read_text(encoding="ascii")
    except FileNotFoundError:
        pass
    time.sleep(0.005)
os._exit(0)
"""
    try:
        result = subprocess.run(command(task, output, 5, [
            "env", f"R3_G_05_TEST_DESCENDANT_PID={descendant_pid_path}",
            sys.executable, "-c", source,
        ]), stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=10, check=False)
        descendant_pid = int(descendant_pid_path.read_text(encoding="ascii"))
        value = record(output)
        if (result.returncode != 72
                or value["reason"] != "descendants-survived-inner-exit"
                or not value["targetSessionEmpty"]
                or descendant_pid not in value["reapedSessionChildPids"]
                or value["reapedSessionChildCount"] < 1
                or session_members(value["sessionId"])
                or Path(f"/proc/{descendant_pid}").exists()):
            raise AssertionError(f"adopted zombie was not reaped before empty proof: {value}")
        require_watchdog_shape(output, value, successful=False)
        if unrelated.poll() is not None:
            raise AssertionError("adopted-zombie teardown touched an unrelated session")
    finally:
        if unrelated.poll() is None:
            os.killpg(os.getpgid(unrelated.pid), signal.SIGKILL)
        unrelated.wait(timeout=5)


def run_stopped_tree_case(task: Path, directory: Path, *, pressure: bool) -> None:
    name = "stopped-tree-pressure" if pressure else "stopped-tree-timeout"
    output = directory / name
    output.mkdir()
    pid_path = directory / f"{name}.pids"
    unrelated = subprocess.Popen(["sleep", "30"], start_new_session=True)
    os.kill(unrelated.pid, signal.SIGSTOP)
    source = """
import os
import pathlib
import signal

path = pathlib.Path(os.environ["R3_G_05_TEST_STOPPED_PIDS"])
child = os.fork()
if child == 0:
    os.setpgid(0, 0)
    with path.open("a", encoding="ascii") as stream:
        stream.write(f"{os.getpid()}\\n")
        stream.flush()
        os.fsync(stream.fileno())
    os.kill(os.getpid(), signal.SIGSTOP)
    os._exit(0)
with path.open("a", encoding="ascii") as stream:
    stream.write(f"{os.getpid()}\\n")
    stream.flush()
    os.fsync(stream.fileno())
os.kill(os.getpid(), signal.SIGSTOP)
os._exit(0)
"""
    try:
        result = subprocess.run(command(task, output, 5 if pressure else 1, [
            "env", f"R3_G_05_TEST_STOPPED_PIDS={pid_path}",
            sys.executable, "-c", source,
        ], watchdog_pressure=pressure), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=10, check=False)
        value = record(output)
        target_pids = {int(pid) for pid in pid_path.read_text(encoding="ascii").splitlines()}
        expected_reason = "watchdog-failure" if pressure else "wall-timeout"
        unrelated_state = Path(f"/proc/{unrelated.pid}/stat").read_text(
            encoding="ascii").split(") ", 1)[1].split()[0]
        if (result.returncode == 0 or value["reason"] != expected_reason
                or not value["targetSessionEmpty"] or session_members(value["sessionId"])
                or any(Path(f"/proc/{pid}").exists() for pid in target_pids)
                or unrelated_state not in ("T", "t")):
            raise AssertionError(f"{name} failed stopped-generation teardown: {value}")
        require_watchdog_shape(output, value, successful=False)
    finally:
        if unrelated.poll() is None:
            os.killpg(os.getpgid(unrelated.pid), signal.SIGKILL)
        unrelated.wait(timeout=5)


def run_historically_reaped_case(task: Path, directory: Path) -> None:
    output = directory / "historically-reaped-before-leader-exit"
    output.mkdir()
    descendant_pid_path = directory / "historically-reaped.pid"
    source = """
import os
import pathlib
import time

pid_path = pathlib.Path(os.environ["R3_G_05_TEST_DESCENDANT_PID"])
intermediate = os.fork()
if intermediate == 0:
    descendant = os.fork()
    if descendant == 0:
        pid_path.write_text(str(os.getpid()), encoding="ascii")
        os._exit(0)
    os._exit(0)
os.waitpid(intermediate, 0)
deadline = time.monotonic() + 3
descendant = None
while descendant is None:
    try:
        descendant = int(pid_path.read_text(encoding="ascii"))
    except (FileNotFoundError, ValueError):
        pass
    if time.monotonic() >= deadline:
        os._exit(94)
    if descendant is None:
        time.sleep(0.005)
while pathlib.Path(f"/proc/{descendant}").exists():
    if time.monotonic() >= deadline:
        os._exit(93)
    time.sleep(0.005)
os._exit(0)
"""
    result = subprocess.run(command(task, output, 5, [
        "env", f"R3_G_05_TEST_DESCENDANT_PID={descendant_pid_path}",
        sys.executable, "-c", source,
    ]), stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=10, check=False)
    descendant_pid = int(descendant_pid_path.read_text(encoding="ascii"))
    value = record(output)
    if (result.returncode != 0 or value["reason"] != "inner-success"
            or descendant_pid not in value["reapedSessionChildPids"]
            or descendant_pid in value["exitTimeDescendantPids"]
            or not value["targetSessionEmpty"] or session_members(value["sessionId"])):
        raise AssertionError(
            f"historical reaping caused a false descendant failure: {value}; "
            f"stderr={result.stderr!r}")
    require_watchdog_shape(output, value, successful=True)


def run_outer_session_rollback_case(task: Path, directory: Path) -> None:
    output = directory / "outer-session-first-writer-rollback"
    output.mkdir()
    (output / "records").mkdir()
    attacker = b'{"attacker":"first-writer"}\n'
    (output / "outer-session.json").write_bytes(attacker)
    (output / "raw-stage.json").write_text(
        '{"active":true,"schema":"R3-G-05-raw-stage-v1",'
        '"stage":"integrity-manifest"}\n', encoding="ascii")
    payload_marker = directory / "outer-session-rollback.payload-ran"
    source = "import pathlib,sys; pathlib.Path(sys.argv[1]).write_text('ran')"
    result = subprocess.run(command(task, output, 5, [
        sys.executable, "-c", source, str(payload_marker),
    ]), stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=10, check=False)
    if (result.returncode == 0 or not payload_marker.is_file()
            or (output / "outer-session.json").read_bytes() != attacker
            or (output / "records/watchdog.done").exists()
            or not (output / "raw-stage.json").is_file()
            or (output / "outer-success.json").exists()):
        raise AssertionError("failed outer-session publication retained success-shaped state")
    publish_raw_failure(output, {
        "schema": "R3-G-05-raw-failure-v1",
        "stage": "integrity-manifest",
        "exitStatus": result.returncode,
    })
    try:
        complete_outer(task.parents[1], output)
    except SystemExit as error:
        if "refuses a failure marker" not in str(error):
            raise
    else:
        raise AssertionError("failure-shaped rollback completed an outer success")


def run_watchdog_pressure_case(task: Path, directory: Path) -> None:
    output = directory / "natural-watchdog-pressure"
    output.mkdir()
    result = subprocess.run(command(task, output, 5, [
        "bash", "-c", "trap '' TERM; while :; do :; done",
    ], watchdog_pressure=True), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        timeout=10, check=False)
    value = record(output)
    watchdog = json.loads((output / "records/watchdog.json").read_text(encoding="utf-8"))
    if (result.returncode == 0 or value["reason"] != "watchdog-failure"
            or value["watchdogStatus"] != 70 or not value["targetSessionEmpty"]
            or watchdog.get("reason") != "injected-resource-pressure"
            or watchdog.get("sessionTerminationProven") is not False):
        raise AssertionError(f"natural watchdog pressure lacks exact final status: {value}")
    require_watchdog_shape(output, value, successful=False)


def run_launcher_hard_kill_case(task: Path, directory: Path) -> None:
    output = directory / "launcher-hard-kill-fallback"
    output.mkdir()
    unrelated = subprocess.Popen(["sleep", "30"], start_new_session=True)
    supervisor = subprocess.Popen(command(task, output, 10, [
        "bash", "-c", "set -m; (trap '' TERM; while :; do sleep 1; done) & "
        "(while :; do sleep 1; done) & wait",
    ]), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    try:
        watchdog_record = output / "records/watchdog.json"
        deadline = time.monotonic() + 3
        while time.monotonic() < deadline and not watchdog_record.is_file():
            time.sleep(0.02)
        value = json.loads(watchdog_record.read_text(encoding="utf-8"))
        target_session = value["sessionId"]
        supervisor.kill()
        supervisor.wait(timeout=3)
        deadline = time.monotonic() + 8
        while time.monotonic() < deadline:
            value = json.loads(watchdog_record.read_text(encoding="utf-8"))
            if value.get("reason") == "launcher-owner-failure" and not session_members(target_session):
                break
            time.sleep(0.05)
        else:
            raise AssertionError("watchdog did not fall back after a hard-killed launcher")
        deadline = time.monotonic() + 3
        while process_alive(value["watchdogPid"]) and time.monotonic() < deadline:
            time.sleep(0.02)
        if process_alive(value["watchdogPid"]):
            raise AssertionError("fallback watchdog did not exit after its final record")
        if (output / "records/watchdog.done").exists():
            raise AssertionError("hard-killed launcher disarmed its fallback watchdog")
        if unrelated.poll() is not None:
            raise AssertionError("launcher hard-kill fallback touched an unrelated session")
    finally:
        if supervisor.poll() is None:
            supervisor.kill()
            supervisor.wait(timeout=3)
        if unrelated.poll() is None:
            os.killpg(os.getpgid(unrelated.pid), signal.SIGKILL)
        unrelated.wait(timeout=5)


def run_stopped_hard_kill_case(task: Path, directory: Path) -> None:
    output = directory / "stopped-tree-launcher-hard-kill"
    output.mkdir()
    pid_path = directory / "stopped-tree-launcher-hard-kill.pids"
    unrelated = subprocess.Popen(["sleep", "30"], start_new_session=True)
    os.kill(unrelated.pid, signal.SIGSTOP)
    source = """
import os
import pathlib
import signal

path = pathlib.Path(os.environ["R3_G_05_TEST_STOPPED_PIDS"])
child = os.fork()
if child == 0:
    os.setpgid(0, 0)
    with path.open("a", encoding="ascii") as stream:
        stream.write(f"{os.getpid()}\\n")
        stream.flush()
        os.fsync(stream.fileno())
    os.kill(os.getpid(), signal.SIGSTOP)
    os._exit(0)
with path.open("a", encoding="ascii") as stream:
    stream.write(f"{os.getpid()}\\n")
    stream.flush()
    os.fsync(stream.fileno())
os.kill(os.getpid(), signal.SIGSTOP)
os._exit(0)
"""
    supervisor = subprocess.Popen(command(task, output, 10, [
        "env", f"R3_G_05_TEST_STOPPED_PIDS={pid_path}",
        sys.executable, "-c", source,
    ]), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    target_pids: set[int] = set()
    target_session: int | None = None
    try:
        deadline = time.monotonic() + 5
        while time.monotonic() < deadline:
            try:
                target_pids = {
                    int(pid) for pid in pid_path.read_text(encoding="ascii").splitlines()
                }
            except FileNotFoundError:
                target_pids = set()
            if len(target_pids) == 2 and all(
                    Path(f"/proc/{pid}").exists() and
                    Path(f"/proc/{pid}/stat").read_text(encoding="ascii").split(
                        ") ", 1)[1].split()[0] in ("T", "t")
                    for pid in target_pids):
                break
            time.sleep(0.02)
        else:
            raise AssertionError("stopped hard-kill target did not become ready")
        watchdog_record = output / "records/watchdog.json"
        deadline = time.monotonic() + 3
        while time.monotonic() < deadline and not watchdog_record.is_file():
            time.sleep(0.02)
        value = json.loads(watchdog_record.read_text(encoding="utf-8"))
        target_session = value["sessionId"]
        supervisor.kill()
        supervisor.wait(timeout=3)
        deadline = time.monotonic() + 8
        while time.monotonic() < deadline:
            value = json.loads(watchdog_record.read_text(encoding="utf-8"))
            if (value.get("reason") == "launcher-owner-failure"
                    and not session_members(target_session)
                    and not any(Path(f"/proc/{pid}").exists() for pid in target_pids)):
                break
            time.sleep(0.05)
        else:
            raise AssertionError(
                "watchdog did not kill the stopped session after launcher hard kill")
        unrelated_state = Path(f"/proc/{unrelated.pid}/stat").read_text(
            encoding="ascii").split(") ", 1)[1].split()[0]
        if unrelated_state not in ("T", "t"):
            raise AssertionError("stopped hard-kill fallback touched an unrelated session")
        deadline = time.monotonic() + 3
        while process_alive(value["watchdogPid"]) and time.monotonic() < deadline:
            time.sleep(0.02)
        if process_alive(value["watchdogPid"]):
            raise AssertionError("stopped hard-kill fallback watchdog did not exit")
        if (output / "records/watchdog.done").exists():
            raise AssertionError("hard-killed launcher disarmed its stopped-target watchdog")
    finally:
        if supervisor.poll() is None:
            supervisor.kill()
            supervisor.wait(timeout=3)
        if target_session is not None:
            for pid in session_members(target_session):
                try:
                    os.kill(pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
        for pid in target_pids:
            try:
                os.kill(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        if unrelated.poll() is None:
            os.killpg(os.getpgid(unrelated.pid), signal.SIGKILL)
        unrelated.wait(timeout=5)


def main() -> None:
    task = Path(__file__).resolve().parent
    try:
        with tempfile.TemporaryDirectory(prefix="r3-g-05-launcher-test-") as temporary:
            directory = Path(temporary)
            run_immediate_success_stress(task, directory)
            run_preexecution_refusal_cases(task, directory)
            run_wait_case(task, directory, "success", 0)
            run_wait_case(task, directory, "failure", 37)
            run_tree_case(task, directory, "timeout-multiple-process-groups", watchdog_crash=False)
            run_tree_case(task, directory, "watchdog-fallback-multiple-process-groups", watchdog_crash=True)
            run_launcher_failure_case(task, directory)
            run_adopted_zombie_case(task, directory)
            run_historically_reaped_case(task, directory)
            run_stopped_tree_case(task, directory, pressure=False)
            run_stopped_tree_case(task, directory, pressure=True)
            run_outer_session_rollback_case(task, directory)
            run_watchdog_pressure_case(task, directory)
            run_launcher_hard_kill_case(task, directory)
            run_stopped_hard_kill_case(task, directory)
    finally:
        for fd in DESCRIPTOR_OWNER_FDS:
            os.close(fd)
    print("R3-G-05 waiting whole-session launcher self-test: pass")


if __name__ == "__main__":
    main()
