#!/usr/bin/env python3
"""Acceptance gate for the documentation-owned composition fixture."""

from __future__ import annotations

import json
import os
from pathlib import Path
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import GateError, entry, krs_gate  # noqa: E402
from support.krs import Invocation, build  # noqa: E402
from support.packages import check_packages  # noqa: E402
from support.process import run  # noqa: E402
from support.tools import checkout_scratch, z3_environment  # noqa: E402


HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "Cargo.toml"


def environment() -> dict[str, str]:
    return {**z3_environment(), "CARGO_TERM_COLOR": "never"}


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


def verify_definition_queries(first: Path, configured: Path, gate: Path, env: dict[str, str]) -> None:
    expected = json.loads((HERE / "definition-checks.json").read_bytes())
    with krs_gate.Session(gate, environment=env) as session:
        descriptors = session.ir_query(first, {"kind": "descriptors"})["rows"]
        packages = {row["cargo_name"] for row in descriptors}
        if not set(expected["packages"]).issubset(packages):
            raise GateError(f"composition does not contain both semantic packages: {packages}")
        modules = session.ir_query(first, {"kind": "modules"})["rows"]
        root = [row for row in modules if row["name"] == expected["root_module"]]
        if len(root) != 1 or expected["base_module"] not in root[0]["imports"]:
            raise GateError(f"composition omits its dependency import: {modules}")
        productions = session.ir_query(first, {"kind": "productions"})["rows"]
        facts = [{key: row[key] for key in ("sort", "symbol", "terminals")} for row in productions]
        for production in expected["productions"]:
            if production not in facts:
                raise GateError(f"composition omits dependency syntax or stable identity: {production}")
        rules = session.ir_query(first, {"kind": "sentences", "module": expected["root_module"], "sentence_kind": "rule"})["rows"]
        if not any(row["body"] == expected["rule_body"] for row in rules):
            raise GateError(f"composition omits the cross-package transition: {rules}")
        configured_productions = session.ir_query(configured, {"kind": "productions"})["rows"]
        normal_facts = [{key: row[key] for key in ("sort", "terminals")} for row in productions]
        configured_facts = [{key: row[key] for key in ("sort", "terminals")} for row in configured_productions]
        if expected["configured_production"] in normal_facts or expected["configured_production"] not in configured_facts:
            raise GateError("cfg-selected production is not isolated to configured emission")


def main() -> None:
    target = checkout_scratch() / "tour-composition-root-target"
    env = {**environment(), "CARGO_TARGET_DIR": os.fspath(target)}
    binary = build(env)
    gate = krs_gate.configured_or_build(target)
    check_packages("tour-composition", krs=binary, env=env, target_dir=target)
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
        verify_definition_queries(first, configured_first, gate, env)
    print("PASS emission: deterministic composition and dual cfg-value artifacts")


if __name__ == "__main__":
    entry("tour-composition", main, errors=(OSError, ValueError, KeyError))
