#!/usr/bin/env python3
"""Pin the tour's focused negative diagnostics to exact authored tokens."""

from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError, entry  # noqa: E402
from support.diagnostics import cargo_primary_span, envelopes, krs_diagnostics  # noqa: E402
from support.krs import Invocation, build  # noqa: E402
from support.packages import check_packages  # noqa: E402
from support.process import compact, render, run  # noqa: E402
from support.tools import checkout_scratch, executable, z3_environment  # noqa: E402


HERE = Path(__file__).resolve().parent
MACRO_NEGATIVES = ROOT / "crates" / "krs-macros" / "tests" / "fixtures" / "negative"


def run_failing(command: list[str | Path]) -> subprocess.CompletedProcess[str]:
    """Run a command the negative case requires to fail."""

    result = run(command, environment=z3_environment(), check=False)
    if result.returncode == 0:
        raise GateError(f"command should fail: {render(command)}\n{compact(result)}")
    return result


def check_rust_negative(binary: str, message: str, token: str) -> None:
    result = run_failing(
        [
            executable("cargo"),
            "check",
            "--locked",
            "--offline",
            "--manifest-path",
            MACRO_NEGATIVES / "Cargo.toml",
            "--bin",
            binary,
            "--message-format=json",
        ],
    )
    span = cargo_primary_span(result.stdout)
    if span.message != message:
        raise GateError(f"{binary}: diagnostic changed: {span.message!r}")
    source = MACRO_NEGATIVES / span.file_name
    selected = source.read_bytes()[span.byte_start:span.byte_end].decode()
    if selected != token:
        raise GateError(f"{binary}: expected authored token {token!r}, got {selected!r}")


def check_overlap(binary: Path) -> None:
    result = run_failing(
        Invocation(binary, HERE / "Cargo.toml", "krs-tour-negatives", "main").argv("check"),
    )
    diagnostics = envelopes(result.stderr)
    if len(diagnostics) != 1:
        raise GateError(f"overlap: expected one JSON diagnostic line, got {len(diagnostics)}")
    typed = krs_diagnostics(result.stderr)
    if len(typed) != 1:
        raise GateError(f"overlap: expected one KRS diagnostic, got {len(typed)}")
    diagnostic = typed[0]
    expected = {
        "schema_version": 1,
        "stage": "analysis",
        "code": "krs::analysis::overlapping-rule-heads",
        "severity": "error",
    }
    for field, value in expected.items():
        if getattr(diagnostic, field) != value:
            raise GateError(f"overlap: {field} changed: {getattr(diagnostic, field)!r}")
    selected = diagnostic.selected_bytes(HERE).decode()
    if selected != "Foo":
        raise GateError(f"overlap: second authored head span changed: {selected!r}")
    if "second_foo" not in diagnostic.message:
        raise GateError("overlap diagnostic does not identify the second stable rule")


def main() -> None:
    target = checkout_scratch() / "tour-negatives-root-target"
    environment = {**z3_environment(), "CARGO_TARGET_DIR": os.fspath(target)}
    binary = build(environment)
    check_packages("tour-negatives", env=environment, target_dir=target)
    check_overlap(binary)
    print("PASS overlap: structured analysis code and exact second Foo head")
    cases = (
        (
            "readable_missing_cell",
            "unsupported fixed configuration field: wrapper-free configurations require `#[k::cell]` on every plain field",
            "renamed_krs",
        ),
        (
            "initializer_control_flow",
            "unsupported declarative initializer body: statements, semicolons, control flow, mutation, and early return are forbidden",
            "if",
        ),
        (
            "malformed_readable_family",
            "invalid enum precedence chain: enum variant `Other` is missing from the exhaustive chain",
            "Other",
        ),
        (
            "readable_rule_bad_update",
            "the update base must be the cell `env`",
            "other",
        ),
    )
    for binary, message, token in cases:
        check_rust_negative(binary, message, token)
        print(f"PASS {binary}: pinned message and authored token {token!r}")


if __name__ == "__main__":
    entry("tour-negatives", main, errors=(OSError, KeyError, TypeError, ValueError))
