#!/usr/bin/env python3
"""End-to-end C7 bare/explicit associativity qualification."""

from __future__ import annotations

import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
MANIFEST = HERE / "rust-definition" / "Cargo.toml"
PACKAGE = "krs-c7-associativity"
MODULE = "KRS-C7-ASSOCIATIVITY"
K_VERSION = "v7.1.337"


def run(
    command: list[str | Path],
    *,
    env: dict[str, str] | None = None,
    timeout: int = 600,
) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        [str(part) for part in command],
        cwd=ROOT,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
        check=False,
    )


def compact(process: subprocess.CompletedProcess[bytes]) -> str:
    output = b"\n".join(
        part.strip() for part in (process.stdout, process.stderr) if part.strip()
    ).decode("utf-8", errors="replace")
    return re.sub(r"/[A-Za-z0-9_.+@%/=-]+", "<PATH>", output)[:2400]


def require(process: subprocess.CompletedProcess[bytes], operation: str) -> None:
    if process.returncode != 0:
        raise RuntimeError(f"{operation} failed: {compact(process)}")


def main() -> int:
    for name in ("kompile", "kast"):
        executable = shutil.which(name)
        if executable is None:
            raise RuntimeError(f"required pinned K tool `{name}` is unavailable")
        version = run([executable, "--version"], timeout=30)
        require(version, f"{name} --version")
        rendered = (version.stdout + version.stderr).decode("utf-8", errors="replace")
        if K_VERSION not in rendered:
            raise RuntimeError(f"{name} is not pinned to {K_VERSION}")

    with tempfile.TemporaryDirectory(prefix="krs-c7-") as temporary:
        workspace = Path(temporary)
        target = workspace / "target"
        environment = {**os.environ, "CARGO_TARGET_DIR": str(target)}
        build = run(
            ["cargo", "build", "--locked", "-p", "krs-cli", "--bin", "krs"],
            env=environment,
        )
        require(build, "build production krs CLI")
        binary = target / "debug" / "krs"

        emitted = workspace / "emitted"
        base: list[str | Path] = [
            binary,
            "--manifest-path",
            MANIFEST,
            "--package",
            PACKAGE,
            "--definition",
            "main",
        ]
        checked = run([base[0], "check", *base[1:]], env=environment)
        require(checked, "krs check")
        generated = run(
            [base[0], "emit-k", *base[1:], "--output", emitted],
            env=environment,
        )
        require(generated, "krs emit-k")

        source = (emitted / "definition.k").read_text(encoding="utf-8")
        if source.count("syntax non-assoc") != 1:
            raise RuntimeError("emitted definition must contain one explicit non-assoc sentence")

        compiled = workspace / "compiled"
        kompile = run(
            [
                "kompile",
                emitted / "definition.k",
                "--main-module",
                MODULE,
                "--syntax-module",
                MODULE,
                "--backend",
                "llvm",
                "--output-definition",
                compiled,
            ]
        )
        require(kompile, "kompile emitted definition")

        accepted = HERE / "corpus" / "accepted" / "iterated-unary.probe"
        parsed = run(
            [
                "kast",
                "--definition",
                compiled,
                "--module",
                MODULE,
                "--sort",
                "Probe",
                "--output",
                "json",
                accepted,
            ],
            timeout=60,
        )
        require(parsed, "parse iterated unary under bare precedence")

        rejected = HERE / "corpus" / "rejected" / "non-associative-equality.probe"
        failed = run(
            [
                "kast",
                "--definition",
                compiled,
                "--module",
                MODULE,
                "--sort",
                "Probe",
                "--output",
                "json",
                rejected,
            ],
            timeout=60,
        )
        if failed.returncode == 0:
            raise RuntimeError("explicit non_assoc direct nesting unexpectedly parsed")

    print("PASS C7: bare iterated unary accepted; explicit non_assoc nesting rejected")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
        print(f"FAIL C7: {error}", file=sys.stderr)
        raise SystemExit(1) from error
