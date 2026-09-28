"""Build and invoke the workspace KRS command-line binary."""

from __future__ import annotations

from dataclasses import dataclass
import os
from pathlib import Path
import subprocess
from typing import Any, Mapping

from support import ROOT, GateError
from support import process, tools


def build(
    environment: Mapping[str, str] | None = None,
    *,
    target: Path | None = None,
    timeout: float | None = 600,
) -> Path:
    """Build the locked CLI and require Cargo to produce its debug binary.

    The target directory is `target` when given, then `CARGO_TARGET_DIR` from
    `environment`, then the workspace default of `tools.workspace_debug_binary`.
    `--offline` is not implied; a caller that needs it sets `CARGO_NET_OFFLINE`.
    """

    env = {**tools.z3_environment(), **(environment or {})}
    if target is None and "CARGO_TARGET_DIR" in env:
        target = Path(env["CARGO_TARGET_DIR"])
        if not target.is_absolute():
            target = ROOT / target
    if target is None:
        binary = tools.workspace_debug_binary("krs")
    else:
        env["CARGO_TARGET_DIR"] = os.fspath(target)
        binary = target / "debug" / "krs"
    process.run(
        ["cargo", "+stable", "build", "--locked", "-p", "krs-cli", "--bin", "krs"],
        cwd=ROOT,
        environment=env,
        timeout=timeout,
    )
    if not binary.is_file():
        raise GateError(f"Cargo did not produce the KRS binary at {binary}")
    return binary


@dataclass(frozen=True)
class Invocation:
    """The selected KRS definition and its stable CLI argument order."""

    binary: Path
    manifest: Path
    package: str
    definition: str | None = None

    def argv(self, command: str, *extra: os.PathLike[str] | str) -> list[str]:
        """Return the command with its manifest, package, and optional definition."""

        argv = [
            os.fspath(self.binary), command,
            "--manifest-path", os.fspath(self.manifest),
            "--package", self.package,
        ]
        if self.definition is not None:
            argv.extend(("--definition", self.definition))
        argv.extend(os.fspath(argument) for argument in extra)
        return argv

    def run(
        self, command: str, *extra: os.PathLike[str] | str, **run_kwargs: Any
    ) -> subprocess.CompletedProcess[Any]:
        """Run this definition's KRS command through the shared process runner."""

        return process.run(self.argv(command, *extra), **run_kwargs)
