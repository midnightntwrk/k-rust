#!/usr/bin/env python3
"""Acceptance gate for the documentation-owned composition fixture."""

from __future__ import annotations

import json
import os
from pathlib import Path
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import GateError, entry  # noqa: E402
from support.krs import Invocation, build  # noqa: E402
from support.packages import check_packages  # noqa: E402
from support.process import run  # noqa: E402
from support.tools import checkout_scratch, rustfmt_dir, z3_environment  # noqa: E402


HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "Cargo.toml"


def environment() -> dict[str, str]:
    return {
        **z3_environment(),
        "CARGO_TERM_COLOR": "never",
        "PATH": os.pathsep.join((os.fspath(rustfmt_dir()), os.environ.get("PATH", ""))),
    }


def command(
    binary: Path,
    operation: str,
    *extra: os.PathLike[str] | str,
) -> list[os.PathLike[str] | str]:
    return Invocation(binary, MANIFEST, "root-semantics", "main").argv(
        operation, "--dependency", "base-semantics:base", *extra
    )


def artifacts(directory: Path) -> dict[str, bytes]:
    return {
        path.name: path.read_bytes()
        for path in sorted(directory.iterdir())
        if path.is_file()
    }


def main() -> None:
    target = checkout_scratch() / "tour-composition-root-target"
    env = {**environment(), "CARGO_TARGET_DIR": os.fspath(target)}
    binary = build(env)
    check_packages("tour-composition", env=env, target_dir=target)
    run([binary, "fmt", "--check", "--manifest-path", MANIFEST], environment=env)
    run(command(binary, "check"), environment=env)
    first_expansion = run(command(binary, "expand"), environment=env).stdout
    second_expansion = run(command(binary, "expand"), environment=env).stdout
    if first_expansion != second_expansion:
        raise GateError("composed reference expansion is nondeterministic")
    first_configured_expansion = run(
        command(binary, "expand", "--cfg", "tour_mode=extended"), environment=env
    ).stdout
    second_configured_expansion = run(
        command(binary, "expand", "--cfg", "tour_mode=extended"), environment=env
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
        run(command(binary, "emit-k", "--output", first), environment=env)
        run(command(binary, "emit-k", "--output", second), environment=env)
        run(
            command(
                binary,
                "emit-k",
                "--cfg",
                "tour_mode=extended",
                "--output",
                configured_first,
            ),
            environment=env,
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
            environment=env,
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
            "imports ORG-KRS-COMPOSITION-BASE",
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
    entry("tour-composition", main, errors=(OSError, ValueError, KeyError))
