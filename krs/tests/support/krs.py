"""Build and invoke the workspace KRS command-line binary."""

from __future__ import annotations

from dataclasses import dataclass
import json
import os
from pathlib import Path
import subprocess
from typing import Any, Mapping

from support import ROOT, GateError
from support import process, tools
from support.hashing import sha256_file


def build(
    environment: Mapping[str, str] | None = None,
    *,
    timeout: float | None = 600,
) -> Path:
    """Build the locked CLI and require Cargo to produce its debug binary.

    It builds in the shared tool target directory (`tools.tool_target`), whatever
    `CARGO_TARGET_DIR` the caller's `environment` sets for the packages it compiles.
    `--offline` is not implied; a caller that needs it sets `CARGO_NET_OFFLINE`.
    """

    binary = tools.workspace_debug_binary("krs")
    env = {
        **tools.z3_environment(),
        **(environment or {}),
        "CARGO_TARGET_DIR": os.fspath(binary.parents[1]),
    }
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


def fresh_deterministic_emissions(
    invocation: Invocation,
    workspace: Path,
    *,
    extra: tuple[str, ...] = (),
    environment: Mapping[str, str] | None = None,
    timeout: float | None = 600,
) -> tuple[Path, Path]:
    """Run two fresh emissions and require a cached replay of the first emission."""

    outputs = tuple(workspace / name for name in ("emit-a", "emit-b", "emit-replay"))
    run_environment = {**(environment or {}), "KRS_NO_REUSE": "0"}
    for output, expected_reused in zip(outputs, (0, 0, 1), strict=True):
        counters_path = workspace / f"{output.name}.krs-counters.json"
        invocation.run(
            "emit-k", *extra, "--output", output, "--counters", counters_path,
            *(("--no-reuse",) if expected_reused == 0 else ()),
            environment=run_environment,
            timeout=timeout,
        )
        try:
            document = json.loads(counters_path.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, json.JSONDecodeError) as error:
            raise GateError(f"{output.name} counters are missing or invalid: {counters_path}") from error
        if (
            not isinstance(document, dict)
            or set(document) != {"schema", "command", "status", "counters"}
            or document["schema"] != "krs-counters/1"
            or document["command"] != "emit-k"
            or document["status"] != "ok"
            or not isinstance(document["counters"], dict)
            or type(document["counters"].get("result.reused")) is not int
            or document["counters"]["result.reused"] != expected_reused
        ):
            raise GateError(f"{output.name} counters do not report result.reused == {expected_reused}")

    first_files = {path.relative_to(outputs[0]) for path in outputs[0].rglob("*") if path.is_file()}
    replay_files = {path.relative_to(outputs[2]) for path in outputs[2].rglob("*") if path.is_file()}
    differences = first_files ^ replay_files
    if differences:
        raise GateError(f"cached replay differs byte-for-byte: {min(differences).as_posix()}")
    for name in sorted(first_files):
        if sha256_file(outputs[0] / name) != sha256_file(outputs[2] / name):
            raise GateError(f"cached replay differs byte-for-byte: {name.as_posix()}")
    return outputs[0], outputs[1]
