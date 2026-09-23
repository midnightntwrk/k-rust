#!/usr/bin/env python3
"""Acceptance gate for the documentation-owned composition fixture."""

from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
MANIFEST = HERE / "Cargo.toml"


class GateError(RuntimeError):
    pass


def run(
    command: list[os.PathLike[str] | str],
    *,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        [os.fspath(part) for part in command],
        cwd=ROOT,
        env=env,
        capture_output=True,
        text=True,
        timeout=600,
        check=False,
    )
    if result.returncode:
        output = "\n".join(
            part.strip()
            for part in (result.stdout, result.stderr)
            if part.strip()
        )
        raise GateError(
            f"command failed ({result.returncode}): "
            f"{' '.join(map(os.fspath, command))}\n{output[:3000]}"
        )
    return result


def environment() -> dict[str, str]:
    env = os.environ.copy()
    candidates = list(Path("/nix/store").glob("*-z3-4.12.5-lib/lib"))
    configured = os.environ.get("KRS_Z3_LIB")
    if configured:
        candidates.insert(0, Path(configured))
    z3 = next((path for path in candidates if path.joinpath("libz3.so").is_file()), None)
    if z3 is None:
        raise GateError("Z3 4.12.5 is unavailable; set KRS_Z3_LIB")
    for name in ("LD_LIBRARY_PATH", "LIBRARY_PATH"):
        env[name] = os.pathsep.join(
            item for item in (os.fspath(z3), env.get(name)) if item
        )
    env["CARGO_TERM_COLOR"] = "never"
    rustup = shutil.which("rustup")
    if rustup:
        located = subprocess.run(
            [rustup, "which", "--toolchain", "stable", "rustfmt"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
        if located.returncode == 0 and located.stdout.strip():
            env["PATH"] = os.pathsep.join(
                (
                    os.fspath(Path(located.stdout.strip()).parent),
                    env.get("PATH", ""),
                )
            )
    return env


def command(
    binary: Path,
    operation: str,
    *extra: os.PathLike[str] | str,
) -> list[os.PathLike[str] | str]:
    return [
        binary,
        operation,
        "--manifest-path",
        MANIFEST,
        "--package",
        "root-semantics",
        "--definition",
        "main",
        "--dependency",
        "base-semantics:base",
        *extra,
    ]


def artifacts(directory: Path) -> dict[str, bytes]:
    return {
        path.name: path.read_bytes()
        for path in sorted(directory.iterdir())
        if path.is_file()
    }


def main() -> None:
    cargo = shutil.which("cargo")
    if cargo is None:
        raise GateError("cargo is unavailable")
    run(
        [
            cargo,
            "check",
            "--locked",
            "--offline",
            "--manifest-path",
            MANIFEST,
            "-p",
            "base-semantics",
            "-p",
            "root-semantics",
        ]
    )
    print("PASS authored: both renamed-dependency packages compile locked/offline")

    env = environment()
    run([cargo, "+stable", "build", "--locked", "-p", "krs-cli", "--bin", "krs"], env=env)
    binary = ROOT / "target" / "debug" / ("krs.exe" if os.name == "nt" else "krs")
    run([binary, "fmt", "--check", "--manifest-path", MANIFEST], env=env)
    run(command(binary, "check"), env=env)
    first_expansion = run(command(binary, "expand"), env=env).stdout
    second_expansion = run(command(binary, "expand"), env=env).stdout
    if first_expansion != second_expansion:
        raise GateError("composed reference expansion is nondeterministic")
    first_configured_expansion = run(
        command(binary, "expand", "--cfg", "tour_mode=extended"), env=env
    ).stdout
    second_configured_expansion = run(
        command(binary, "expand", "--cfg", "tour_mode=extended"), env=env
    ).stdout
    if first_configured_expansion != second_configured_expansion:
        raise GateError("cfg-selected reference expansion is nondeterministic")
    print("PASS KRS: format, composition check, and deterministic expansion")

    with (
        tempfile.TemporaryDirectory(
            prefix="krs-tour-composition-a-"
        ) as first_name,
        tempfile.TemporaryDirectory(
            prefix="krs-tour-composition-b-"
        ) as second_name,
        tempfile.TemporaryDirectory(
            prefix="krs-tour-composition-cfg-a-"
        ) as configured_first_name,
        tempfile.TemporaryDirectory(
            prefix="krs-tour-composition-cfg-b-"
        ) as configured_second_name,
    ):
        first = Path(first_name)
        second = Path(second_name)
        configured_first = Path(configured_first_name)
        configured_second = Path(configured_second_name)
        run(command(binary, "emit-k", "--output", first), env=env)
        run(command(binary, "emit-k", "--output", second), env=env)
        run(
            command(
                binary,
                "emit-k",
                "--cfg",
                "tour_mode=extended",
                "--output",
                configured_first,
            ),
            env=env,
        )
        run(
            command(
                binary,
                "emit-k",
                "--cfg",
                "tour_mode=extended",
                "--output",
                configured_second,
            ),
            env=env,
        )
        emitted = artifacts(first)
        if emitted != artifacts(second):
            raise GateError("composed artifacts are nondeterministic")
        configured = artifacts(configured_first)
        if configured != artifacts(configured_second):
            raise GateError("cfg-selected composed artifacts are nondeterministic")
        bundle = json.loads(emitted["descriptor-bundle.json"])
        packages = {
            descriptor.get("id", {}).get("package", {}).get("cargo_name")
            for descriptor in bundle.get("descriptors", [])
        }
        if not {"base-semantics", "root-semantics"}.issubset(packages):
            raise GateError(f"composition does not contain both semantic packages: {packages}")
        definition = emitted["definition.k"].decode("utf-8")
        expected_composition = (
            "imports ORG-KRS-M1-BASE",
            'syntax BaseCommon ::= "same" "-" "base" [symbol(baseSame)]',
            "rule same - base => same - base",
            'syntax RootCommon ::= "same" "-" "root" [symbol(rootSame)]',
        )
        missing = [sentence for sentence in expected_composition if sentence not in definition]
        if missing:
            raise GateError(
                "emitted composition omits dependency syntax, stable identity, or the "
                f"cross-package rule: {missing}"
            )
        configured_definition = configured["definition.k"].decode("utf-8")
        cfg_production = 'syntax RootCommon ::= "extended" "-" "root"'
        if cfg_production in definition or cfg_production not in configured_definition:
            raise GateError("cfg-selected production is not isolated to configured emission")
    print("PASS emission: deterministic composition and dual cfg-value artifacts")


if __name__ == "__main__":
    try:
        main()
    except (GateError, OSError, ValueError, KeyError, json.JSONDecodeError) as error:
        print(f"FAIL tour-composition: {error}", file=sys.stderr)
        raise SystemExit(1) from error
    print("PASS tour-composition")
