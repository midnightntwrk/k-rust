#!/usr/bin/env python3
"""Executable bridge prototype using Java Claim KORE as a native-shaped fixture."""

from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
UPSTREAM_DEFINITION = (
    ROOT.parent
    / "inspirations/runtimeverification/imp-semantics/src/kimp/kdist/imp-semantics"
)


def main() -> int:
    environment = os.environ.copy()
    environment.update(
        {
            "LC_ALL": "C",
            "LANG": "C",
            "PYTHONDONTWRITEBYTECODE": "1",
            "TMPDIR": "/tmp",
        }
    )
    environment.setdefault("CARGO_TARGET_DIR", "/dev/shm/krs-m3d-target")
    cases = json.loads((HERE / "cases.json").read_text(encoding="utf-8"))["cases"]

    with tempfile.TemporaryDirectory(prefix="krs-m3d-claim-harness-", dir="/tmp") as temporary:
        workspace = Path(temporary)
        skeleton = workspace / "shell-kompiled"
        run(
            [
                required("kompile"),
                str(ROOT / "tests/m3d/fixtures/static-adjunct.k"),
                "-I",
                str(UPSTREAM_DEFINITION),
                "--backend",
                "haskell",
                "--main-module",
                "KRS-M3D-STATIC",
                "--syntax-module",
                "KRS-M3D-STATIC-SYNTAX",
                "--emit-json",
                "--output-definition",
                str(skeleton),
            ],
            environment,
        )

        specs = []
        for case in cases:
            temp_dir = workspace / "source-specs" / case["name"]
            temp_dir.mkdir(parents=True)
            source = (ROOT / case["source_spec"]).resolve(strict=True)
            run(
                [
                    required("kprove"),
                    str(source),
                    "-d",
                    str(skeleton),
                    "-I",
                    str(UPSTREAM_DEFINITION),
                    "-I",
                    str(ROOT / "tests/m3d/fixtures"),
                    "--spec-module",
                    case["source_module"],
                    "--claims",
                    case["source_claim"],
                    "--dry-run",
                    "--temp-dir",
                    str(temp_dir),
                ],
                environment,
            )
            found = list(temp_dir.rglob("spec.kore"))
            if len(found) != 1:
                raise RuntimeError(f"expected one generated spec for {case['name']}: {found}")
            specs.append(found[0])

        fixture = workspace / "native-shaped-definition.kore"
        run(
            [
                "cargo",
                "run",
                "--quiet",
                "--manifest-path",
                str(HERE / "Cargo.toml"),
                "--",
                "fixture-merge",
                str(skeleton / "definition.kore"),
                str(fixture),
                "KRS-M3D-STATIC",
                str(HERE / "cases.json"),
                *map(str, specs),
            ],
            environment,
        )
        run(
            [
                sys.executable,
                str(HERE / "harness.py"),
                "--native-kore",
                str(fixture),
                "--parse-skeleton",
                str(skeleton),
                "--execution-skeleton",
                str(skeleton),
                "--workspace",
                str(workspace / "run"),
            ],
            environment,
            timeout=900,
        )
    print(
        "PASS\tprototype\tnative Claim injection, separated source parsing, "
        "direct proof, and frozen hashes"
    )
    return 0


def required(name: str) -> str:
    executable = shutil.which(name)
    if executable is None:
        raise RuntimeError(f"required tool {name!r} is not on PATH")
    return executable


def run(
    command: list[str], environment: dict[str, str], timeout: int = 300
) -> subprocess.CompletedProcess[str]:
    process = subprocess.run(
        command,
        cwd=ROOT,
        env=environment,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
        check=False,
    )
    if process.stdout:
        print(process.stdout, end="")
    if process.returncode != 0:
        raise RuntimeError(
            f"command failed with rc={process.returncode}: {command!r}\n{process.stderr}"
        )
    return process


if __name__ == "__main__":
    sys.exit(main())
