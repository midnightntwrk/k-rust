"""Subprocess execution for the gate verifiers."""

from __future__ import annotations

import os
from pathlib import Path
import signal
import subprocess
import threading
from typing import Any, Mapping, Sequence

from support import ROOT, GateError


BASE_ENVIRONMENT = {"LC_ALL": "C", "LANG": "C", "PYTHONDONTWRITEBYTECODE": "1"}
"""Variables every command receives, ahead of the caller's own overrides."""

TERMINATION_GRACE_SECONDS = 5
OUTPUT_LIMIT = 6000


def _exit_on_sigterm(signum: int, _frame: object) -> None:
    raise SystemExit(128 + signum)


# Commands run in their own sessions, so a SIGTERM sent to the verifier alone
# would orphan them. Turning it into SystemExit unwinds through `run`, which
# terminates the running command's process group on the way out.
if threading.current_thread() is threading.main_thread() and signal.getsignal(signal.SIGTERM) is signal.SIG_DFL:
    signal.signal(signal.SIGTERM, _exit_on_sigterm)


def render(command: Sequence[str | os.PathLike[str]]) -> str:
    return " ".join(os.fspath(part) for part in command)


def _text(value: str | bytes | None) -> str:
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return value


def compact(process: subprocess.CompletedProcess[Any], limit: int = OUTPUT_LIMIT) -> str:
    """Join the stripped stdout and stderr, keeping both ends when too long.

    A failing build prints its error last, after a long progress log, so the
    tail carries more of the limit than the head.
    """

    output = "\n".join(
        part for part in (_text(process.stdout).strip(), _text(process.stderr).strip()) if part
    )
    if len(output) <= limit:
        return output
    head = limit // 4
    return f"{output[:head]}\n…\n{output[head - limit:]}"


def terminate_group(process: subprocess.Popen[Any]) -> tuple[Any, Any]:
    """Terminate the process's whole session, escalating to SIGKILL, and reap it."""

    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        return process.communicate(timeout=TERMINATION_GRACE_SECONDS)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        return process.communicate()


def run(
    command: Sequence[str | os.PathLike[str]],
    *,
    cwd: Path | None = None,
    environment: Mapping[str, str] | None = None,
    timeout: float | None = 600,
    check: bool = True,
    text: bool = True,
    capture: bool = True,
    input: str | bytes | None = None,
) -> subprocess.CompletedProcess[Any]:
    """Run one command in its own process session and return its result.

    The command runs in `cwd` (the repository root by default) with the current
    environment, then `BASE_ENVIRONMENT`, then `environment` layered on top.
    Output is captured unless `capture` is false, in which case it streams to
    this process's stdout and stderr. A timeout terminates the command's whole
    process group before raising `GateError`, so no grandchild outlives it.
    With `check`, a nonzero exit status raises `GateError` carrying the output.
    """

    argv = [os.fspath(part) for part in command]
    env = {**os.environ, **BASE_ENVIRONMENT, **(environment or {})}
    pipe = subprocess.PIPE if capture else None
    process = subprocess.Popen(
        argv,
        cwd=cwd if cwd is not None else ROOT,
        env=env,
        text=text,
        stdin=subprocess.PIPE if input is not None else None,
        stdout=pipe,
        stderr=pipe,
        start_new_session=True,
    )
    try:
        stdout, stderr = process.communicate(input, timeout=timeout)
    except subprocess.TimeoutExpired as error:
        stdout, stderr = terminate_group(process)
        partial = subprocess.CompletedProcess(argv, -1, stdout, stderr)
        raise GateError(
            f"command timed out after {timeout}s; its process group was terminated: "
            f"{render(argv)}\n{compact(partial)}"
        ) from error
    except BaseException:
        terminate_group(process)
        raise
    result = subprocess.CompletedProcess(argv, process.returncode, stdout, stderr)
    if check and result.returncode != 0:
        raise GateError(f"command failed ({result.returncode}): {render(argv)}\n{compact(result)}")
    return result
