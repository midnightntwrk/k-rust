#!/usr/bin/env python3
"""Task-local zero-backend refusal tests for the R3-G-05 oracle wrapper."""

from __future__ import annotations

import fcntl
import json
import os
import shutil
import subprocess
import tempfile
from pathlib import Path

from cache_integrity import (
    EXACT_FINAL_TIMEOUT_REPORT_WITNESS,
    require_exact_timeout_report,
    require_exact_wall_timeout,
)
from descriptor_owner import process_generation


def require_refusal(
    command: list[str], environment: dict[str, str], witness: str | None,
    *, separate_pgrp: bool = False, pass_fds: tuple[int, ...] = (),
) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        command, env=environment, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=20, check=False,
        preexec_fn=(lambda: os.setpgid(0, 0)) if separate_pgrp else None,
        pass_fds=pass_fds,
    )
    if result.returncode == 0 or (witness is not None and witness not in result.stdout):
        raise AssertionError(
            f"expected refusal containing {witness!r}; code={result.returncode}; output={result.stdout!r}")
    return result


def require_quiet_recovery(result: subprocess.CompletedProcess[str], description: str) -> None:
    if "marker already exists" in result.stdout or "Traceback" in result.stdout:
        raise AssertionError(f"{description} printed duplicate-marker recovery traceback: {result.stdout!r}")


def main() -> None:
    task = Path(__file__).resolve().parent
    root = task.parent.parent
    replay = task / "replay.sh"
    build = task / "build"
    build.mkdir(exist_ok=True)
    cycle_output = build / "cycle-5-r3-g-05n"
    if cycle_output.exists() or cycle_output.is_symlink():
        raise AssertionError("cycle-5 output existed before final-cycle refusal tests")
    production_env = {**os.environ, "R3_G_05_ROOT_AUTHORIZED": "1"}
    for name in ("R3_G_05_TEST_MODE", "R3_G_05_IMPLEMENTATION_HEAD",
                 "R3_G_05_ROOT_AUTHORIZATION_SHA256", "R3_G_05_RAW_INNER"):
        production_env.pop(name, None)
    require_refusal(
        ["bash", str(replay), "raw", str(cycle_output)], production_env,
        "implementation head must be an exact lowercase 40-hex commit ID")
    require_refusal(
        ["bash", str(replay), "raw", str(cycle_output)],
        {**production_env, "R3_G_05_IMPLEMENTATION_HEAD": "0" * 40},
        "does not equal checkout HEAD")
    for cycle in ("4", "6"):
        require_refusal(
            ["bash", str(replay), "raw", str(cycle_output)],
            {**production_env, "R3_G_05_CYCLE_COUNT": cycle},
            "cycle count must be exactly 5")
    require_refusal(
        ["bash", str(replay), "raw", str(cycle_output)],
        {**production_env, "R3_G_05_JAVA_MAX_HEAP_MIB": "1536"},
        "non-test raw heap must be exactly 2048 MiB")
    require_refusal(
        ["bash", str(replay), "raw", str(cycle_output)],
        {**production_env, "R3_G_05_JAVA_ACTIVE_PROCESSORS": "1"},
        "non-test raw processor count must be exactly 2")
    require_refusal(
        ["bash", str(replay), "raw", str(cycle_output)],
        {**production_env, "R3_G_05_WALL_TIMEOUT_SECONDS": "3600"},
        "non-test raw wall timeout must be exactly 7200 seconds")
    require_refusal(
        ["bash", str(replay), "raw", str(build / "cycle-4-r3-g-05l")],
        production_env, "fresh exact cycle-5 path")
    require_refusal(
        ["bash", str(replay), "raw", str(build / "non-exact-final-cycle")],
        production_env, "fresh exact cycle-5 path")
    if cycle_output.exists() or cycle_output.is_symlink():
        raise AssertionError("final-cycle refusal reserved the cycle-5 output")
    for label in ("raw integrity manifest", "final evidence resource policy"):
        for record in ({}, {"wallTimeoutSeconds": 3600}):
            try:
                require_exact_wall_timeout(record, label)
            except SystemExit as error:
                if "exact 7200-second wall timeout" not in str(error):
                    raise AssertionError(f"unexpected exact-timeout refusal: {error}") from error
            else:
                raise AssertionError(f"{label} accepted a missing or altered exact timeout")
    for altered_report in (
        "Cycle 5 used a bounded wall timeout.",
        "",
        EXACT_FINAL_TIMEOUT_REPORT_WITNESS * 2,
    ):
        try:
            require_exact_timeout_report(altered_report)
        except SystemExit as error:
            if "unique exact 7200-second timeout witness" not in str(error):
                raise AssertionError(f"unexpected exact-report refusal: {error}") from error
        else:
            raise AssertionError("altered report with a recomputable hash retained acceptance")
    base_env = {**os.environ, "R3_G_05_TEST_MODE": "1"}
    base_env.pop("R3_G_05_ROOT_AUTHORIZED", None)
    base_env.pop("R3_G_05_ROOT_AUTHORIZATION_SHA256", None)
    base_env.pop("R3_G_05_RAW_INNER", None)
    with tempfile.TemporaryDirectory(prefix="adversarial-", dir=build) as directory:
        owned = Path(directory).resolve()
        output = owned / "raw"
        command = ["bash", str(replay), "raw", str(output)]

        require_refusal(command, base_env, "explicit root authorization")

        existing = owned / "existing"
        existing.mkdir()
        require_refusal(
            ["bash", str(replay), "raw", str(existing)],
            {**base_env, "R3_G_05_ROOT_AUTHORIZED": "1"},
            "raw output already exists",
        )

        outside = owned / "outside"
        outside.mkdir()
        sentinel = outside / "sentinel"
        sentinel.write_text("unchanged\n", encoding="utf-8")
        linked_output = owned / "linked-output"
        linked_output.symlink_to(outside, target_is_directory=True)
        require_refusal(
            ["bash", str(replay), "raw", str(linked_output)],
            {**base_env, "R3_G_05_ROOT_AUTHORIZED": "1"},
            "symlink path component is forbidden",
        )
        dangling_output = owned / "dangling-output"
        dangling_output.symlink_to(owned / "absent-target", target_is_directory=True)
        require_refusal(
            ["bash", str(replay), "raw", str(dangling_output)],
            {**base_env, "R3_G_05_ROOT_AUTHORIZED": "1"},
            "symlink path component is forbidden",
        )
        if sentinel.read_text(encoding="utf-8") != "unchanged\n":
            raise AssertionError("output leaf symlink refusal modified the outside sentinel")

        direct_output = owned / "direct-raw-inner"
        direct_output.mkdir()
        owner_fd = os.open(
            direct_output, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW)
        immediate_fd = os.dup(owner_fd)
        owner_identity = process_generation(os.getpid())
        if owner_identity is None:
            raise AssertionError("direct raw-inner descriptor owner is unavailable")
        output_identity = os.fstat(owner_fd)
        try:
            require_refusal(
                ["bash", str(replay), "raw-inner", str(direct_output)],
                {
                    **base_env,
                    "R3_G_05_ROOT_AUTHORIZED": "1",
                    "R3_G_05_RAW_INNER": "1",
                    "R3_G_05_OUTPUT_FD": str(immediate_fd),
                    "R3_G_05_DESCRIPTOR_OWNER_PID": str(os.getpid()),
                    "R3_G_05_DESCRIPTOR_OWNER_START_TIME": str(
                        owner_identity.start_time),
                    "R3_G_05_DESCRIPTOR_OWNER_FD": str(owner_fd),
                    "R3_G_05_OUTPUT_DEVICE": str(output_identity.st_dev),
                    "R3_G_05_OUTPUT_INODE": str(output_identity.st_ino),
                },
                "dedicated session/process group",
                separate_pgrp=True,
                pass_fds=(immediate_fd,),
            )
        finally:
            os.close(immediate_fd)
            os.close(owner_fd)

        inherited_output = owned / "inherited-java-option"
        inherited_result = require_refusal(
            ["bash", str(replay), "raw", str(inherited_output)],
            {**base_env, "R3_G_05_ROOT_AUTHORIZED": "1", "JAVA_TOOL_OPTIONS": "-Xmx9g"},
            "inherited Java tool options",
        )
        require_quiet_recovery(inherited_result, "inherited-option failure")
        failure = json.loads((inherited_output / "raw-failure.json").read_text(encoding="utf-8"))
        if failure != {"schema": "R3-G-05-raw-failure-v1",
                       "stage": "raw-inner-preflight", "exitStatus": 1}:
            raise AssertionError(f"durable raw failure provenance is invalid: {failure!r}")

        hard_kill = owned / "hard-kill"
        hard_kill_result = require_refusal(
            ["bash", str(replay), "raw", str(hard_kill)],
            {**base_env, "R3_G_05_ROOT_AUTHORIZED": "1", "R3_G_05_TEST_RAW_HARD_KILL": "1"},
            None,
        )
        hard_kill_failure = json.loads(
            (hard_kill / "raw-failure.json").read_text(encoding="utf-8"))
        if (hard_kill_result.returncode != 137
                or hard_kill_failure != {"schema": "R3-G-05-raw-failure-v1",
                                         "stage": "synthetic-hard-kill", "exitStatus": 137}):
            raise AssertionError(
                f"hard-kill stage/status recovery failed: code={hard_kill_result.returncode} "
                f"record={hard_kill_failure!r}")
        require_quiet_recovery(hard_kill_result, "hard-kill wrapper failure")

        exhausted = owned / "exhausted"
        exhausted_result = require_refusal(
            ["bash", str(replay), "raw", str(exhausted)],
            {**base_env, "R3_G_05_ROOT_AUTHORIZED": "1",
             "R3_G_05_TEST_AVAILABLE_KIB": "1", "R3_G_05_TEST_SWAP_FREE_KIB": "1"},
            "less than 4 GiB MemAvailable",
        )
        require_quiet_recovery(exhausted_result, "resource-floor failure")
        exhausted_failure = json.loads((exhausted / "raw-failure.json").read_text(encoding="utf-8"))
        if exhausted_failure.get("stage") != "resource-preflight" or exhausted_failure.get("exitStatus") != 1:
            raise AssertionError("resource refusal did not preserve its named stage and exit status")

        lock_path = owned / "lock"
        lock_path.touch()
        with lock_path.open("r+") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            require_refusal(
                ["bash", str(replay), "raw", str(owned / "lock-contention")],
                {**base_env, "R3_G_05_ROOT_AUTHORIZED": "1",
                 "R3_G_05_TEST_LOCK_FILE": str(lock_path)},
                "another K-in-K backend oracle owns",
            )

        unvalidated = owned / "unvalidated"
        unvalidated.mkdir()
        require_refusal(
            ["bash", str(replay), "publish", str(unvalidated)],
            base_env,
            "terminal success record",
        )

        # A stale manifest-bound provisional file must be rejected before publish.
        stale = owned / "stale"
        stale.mkdir()
        (stale / "raw-success.json").write_text(
            json.dumps({"schema": "R3-G-05-raw-success-v1", "terminal": True}) + "\n",
            encoding="utf-8")
        (stale / "integrity-manifest.json").write_text("{}\n", encoding="utf-8")
        require_refusal(
            ["bash", str(replay), "publish", str(stale)], base_env,
            "raw integrity manifest schema mismatch",
        )

        failed = owned / "failed"
        failed.mkdir()
        (failed / "raw-failure.json").write_text(
            json.dumps({"schema": "R3-G-05-raw-failure-v1", "stage": "synthetic",
                        "exitStatus": 37}) + "\n", encoding="utf-8")
        (failed / "integrity-manifest.json").write_text("{}\n", encoding="utf-8")
        require_refusal(
            ["bash", str(replay), "publish", str(failed)], base_env,
            "terminal failure marker",
        )

        absent_success = owned / "absent-success"
        absent_success.mkdir()
        (absent_success / "integrity-manifest.json").write_text("{}\n", encoding="utf-8")
        require_refusal(
            ["bash", str(replay), "publish", str(absent_success)], base_env,
            "terminal success record",
        )

        unterminated = owned / "unterminated"
        unterminated.mkdir()
        (unterminated / "raw-success.json").write_text(
            json.dumps({"schema": "R3-G-05-raw-success-v1", "terminal": True}) + "\n",
            encoding="utf-8")
        (unterminated / "raw-stage.json").write_text(
            json.dumps({"schema": "R3-G-05-raw-stage-v1", "stage": "synthetic"}) + "\n",
            encoding="utf-8")
        (unterminated / "integrity-manifest.json").write_text("{}\n", encoding="utf-8")
        require_refusal(
            ["bash", str(replay), "publish", str(unterminated)], base_env,
            "unterminated stage record",
        )

    # TemporaryDirectory owns and removes only its explicit ignored build child.
    if build.exists() and not any(build.iterdir()):
        build.rmdir()
    print("R3-G-05 raw refusal/publish adversarial tests: pass")


if __name__ == "__main__":
    main()
