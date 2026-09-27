"""Whole-process-tree measurement of one command.

The preferred method places each measured command in its own cgroup v2 child
of a delegated systemd scope and reads the child's `memory.peak` and
`cpu.stat` after every process in it has exited. The numbers therefore cover
Cargo, every rustc, build scripts, the collector, and the linker together.

The harness enters the scope by re-executing itself under
`systemd-run --user --scope -p Delegate=yes`, copying the tightest memory
limits of its current cgroup and ancestors onto the new scope so that a run
started inside a memory-limited slice cannot escape that limit. Inside the
scope the harness moves itself into a `supervisor` child (cgroup v2 forbids
processes in a cgroup that distributes controllers to children), enables the
memory controller for the children, and creates one `run-N` child per
measured command. The command is moved into its child between `fork` and
`exec`, so no process changes cgroup while it is timed.

When delegation is unavailable the fallback records wall time and the
`wait4` resource usage of the reaped tree (user and system CPU of every
waited-for descendant) and reports peak memory as unavailable. A single
process's maximum resident set size never stands in for the tree peak.
"""

from __future__ import annotations

from dataclasses import dataclass
import os
from pathlib import Path
import signal
import subprocess
import threading
import time
from typing import Mapping, Sequence


SCOPE_VARIABLE = "KRS_PERF_SCOPE"
"""Set by the harness when it re-executes itself inside a delegated scope."""

CGROUP_ROOT = Path("/sys/fs/cgroup")

CGROUP_METHOD = "cgroup-v2"
RUSAGE_METHOD = "wait4-rusage"


@dataclass(frozen=True)
class Measurement:
    exit_status: int
    """The exit code, or the negative signal number that ended the command."""
    timed_out: bool
    wall_seconds: float
    user_seconds: float | None
    sys_seconds: float | None
    peak_memory_bytes: int | None
    method: str


def current_cgroup() -> Path | None:
    try:
        line = Path("/proc/self/cgroup").read_text(encoding="utf-8").splitlines()[0]
    except (OSError, IndexError):
        return None
    if not line.startswith("0::"):
        return None
    return CGROUP_ROOT / line[3:].lstrip("/")


def inherited_limits(start: Path | None = None) -> list[str]:
    """systemd properties that copy the tightest memory limits above `start`."""

    directory = start if start is not None else current_cgroup()
    properties: list[str] = []
    if directory is None:
        return properties
    for key, name in (("max", "MemoryMax"), ("high", "MemoryHigh"), ("swap.max", "MemorySwapMax")):
        limit: int | None = None
        cursor = directory
        while cursor == CGROUP_ROOT or CGROUP_ROOT in cursor.parents:
            try:
                value = (cursor / f"memory.{key}").read_text(encoding="utf-8").strip()
            except OSError:
                value = ""
            if value.isdigit() and (limit is None or int(value) < limit):
                limit = int(value)
            if cursor == CGROUP_ROOT:
                break
            cursor = cursor.parent
        if limit is not None:
            properties.append(f"{name}={limit}")
    return properties


def scope_command(argv: Sequence[str]) -> list[str]:
    """The `systemd-run` command that re-executes `argv` inside a delegated scope."""

    command = ["systemd-run", "--user", "--scope", "--quiet", "-p", "Delegate=yes"]
    for prop in inherited_limits():
        command += ["-p", prop]
    return [*command, "--", *argv]


class Meter:
    """Runs commands serially and measures each one's whole process tree."""

    def __init__(self, scope: Path | None, note: str | None = None) -> None:
        self.scope = scope
        self.note = note
        self._next = 0

    @property
    def method(self) -> str:
        return CGROUP_METHOD if self.scope is not None else RUSAGE_METHOD

    @classmethod
    def open(cls) -> "Meter":
        """Use the delegated scope the harness runs in, or fall back to `wait4`."""

        if os.environ.get(SCOPE_VARIABLE) != "1":
            return cls(None, "not running inside a delegated scope")
        scope = current_cgroup()
        if scope is None:
            return cls(None, "cgroup v2 is unavailable")
        try:
            supervisor = scope / "supervisor"
            supervisor.mkdir(exist_ok=True)
            (supervisor / "cgroup.procs").write_text(str(os.getpid()), encoding="utf-8")
            (scope / "cgroup.subtree_control").write_text("+memory", encoding="utf-8")
            probe = scope / "run-probe"
            probe.mkdir(exist_ok=True)
            readable = (probe / "memory.peak").is_file() and (probe / "cpu.stat").is_file()
            probe.rmdir()
        except OSError as error:
            return cls(None, f"the scope cannot delegate a memory cgroup: {error}")
        if not readable:
            return cls(None, "the scope's children lack memory.peak or cpu.stat")
        return cls(scope)

    def run(
        self,
        argv: Sequence[str | os.PathLike[str]],
        *,
        cwd: Path,
        environment: Mapping[str, str],
        log: Path,
        timeout: float,
    ) -> Measurement:
        command = [os.fspath(part) for part in argv]
        log.parent.mkdir(parents=True, exist_ok=True)
        group: Path | None = None
        if self.scope is not None:
            self._next += 1
            group = self.scope / f"run-{self._next}"
            group.mkdir()
        procs = os.fspath(group / "cgroup.procs") if group is not None else None

        def enter_group() -> None:
            if procs is not None:
                with open(procs, "w", encoding="utf-8") as handle:
                    handle.write(str(os.getpid()))

        timed_out = threading.Event()
        with log.open("wb") as output:
            start = time.monotonic()
            process = subprocess.Popen(
                command,
                cwd=cwd,
                env=dict(environment),
                stdin=subprocess.DEVNULL,
                stdout=output,
                stderr=subprocess.STDOUT,
                start_new_session=True,
                preexec_fn=enter_group,
            )

            def expire() -> None:
                timed_out.set()
                _kill(process.pid, group)

            timer = threading.Timer(timeout, expire)
            timer.start()
            try:
                _, status, usage = os.wait4(process.pid, 0)
            except BaseException:
                _kill(process.pid, group)
                raise
            finally:
                timer.cancel()
            wall = time.monotonic() - start
            process.returncode = os.waitstatus_to_exitcode(status)
        # Background descendants (none are expected) would keep the cgroup
        # populated and inflate the peak; end them before reading.
        if group is not None:
            _drain(group)
            peak = int((group / "memory.peak").read_text(encoding="utf-8").strip())
            stat = _cpu_stat(group)
            user = stat.get("user_usec", 0) / 1e6
            system = stat.get("system_usec", 0) / 1e6
            try:
                group.rmdir()
            except OSError:
                pass
            return Measurement(process.returncode, timed_out.is_set(), wall, user, system, peak, CGROUP_METHOD)
        return Measurement(
            process.returncode, timed_out.is_set(), wall, usage.ru_utime, usage.ru_stime, None, RUSAGE_METHOD
        )


def _cpu_stat(group: Path) -> dict[str, int]:
    values: dict[str, int] = {}
    for line in (group / "cpu.stat").read_text(encoding="utf-8").splitlines():
        key, _, value = line.partition(" ")
        if value.strip().isdigit():
            values[key] = int(value)
    return values


def _kill(pid: int, group: Path | None) -> None:
    if group is not None:
        try:
            (group / "cgroup.kill").write_text("1", encoding="utf-8")
            return
        except OSError:
            pass
    try:
        os.killpg(pid, signal.SIGKILL)
    except ProcessLookupError:
        pass


def _drain(group: Path, grace: float = 10.0) -> None:
    def populated() -> bool:
        for line in (group / "cgroup.events").read_text(encoding="utf-8").splitlines():
            if line.startswith("populated "):
                return line.split()[1] == "1"
        return False

    if not populated():
        return
    (group / "cgroup.kill").write_text("1", encoding="utf-8")
    deadline = time.monotonic() + grace
    while populated() and time.monotonic() < deadline:
        time.sleep(0.05)
