#!/usr/bin/env python3
"""Pin the tour's focused negative diagnostics to exact authored tokens."""

from __future__ import annotations

from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError, entry  # noqa: E402
from support.diagnostics import envelopes  # noqa: E402
from support.krs import Invocation, build  # noqa: E402
from support.process import compact, render, run  # noqa: E402
from support.tools import executable, z3_environment  # noqa: E402


HERE = Path(__file__).resolve().parent
MACRO_NEGATIVES = ROOT / "crates" / "krs-macros" / "tests" / "fixtures" / "negative"


def run_failing(command: list[str | Path]) -> subprocess.CompletedProcess[str]:
    """Run a command the negative case requires to fail."""

    result = run(command, environment=z3_environment(), check=False)
    if result.returncode == 0:
        raise GateError(f"command should fail: {render(command)}\n{compact(result)}")
    return result


def primary_error(output: str) -> dict[str, object]:
    for message in envelopes(output):
        if message.get("reason") == "compiler-message":
            diagnostic = message["message"]
            if diagnostic.get("level") == "error":
                return diagnostic
    raise GateError("Cargo JSON contained no error diagnostic")


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
    diagnostic = primary_error(result.stdout)
    if diagnostic.get("message") != message:
        raise GateError(f"{binary}: diagnostic changed: {diagnostic.get('message')!r}")
    spans = [span for span in diagnostic.get("spans", []) if span.get("is_primary")]
    if len(spans) != 1:
        raise GateError(f"{binary}: expected one primary authored span, got {len(spans)}")
    span = spans[0]
    source = MACRO_NEGATIVES / str(span["file_name"])
    selected = source.read_bytes()[int(span["byte_start"]):int(span["byte_end"])].decode()
    if selected != token:
        raise GateError(f"{binary}: expected authored token {token!r}, got {selected!r}")


def check_overlap() -> None:
    binary = build()
    result = run_failing(
        Invocation(binary, HERE / "Cargo.toml", "krs-tour-negatives", "main").argv("check"),
    )
    diagnostics = envelopes(result.stderr)
    if len(diagnostics) != 1:
        raise GateError(f"overlap: expected one JSON diagnostic line, got {len(diagnostics)}")
    diagnostic = diagnostics[0]
    expected = {
        "schema_version": 1,
        "stage": "analysis",
        "code": "overlapping-rule-heads",
        "severity": "error",
    }
    for field, value in expected.items():
        if diagnostic.get(field) != value:
            raise GateError(f"overlap: {field} changed: {diagnostic.get(field)!r}")
    authored = diagnostic["authored_range"]
    source = HERE / str(authored["file"]["package_relative_path"])
    selected = source.read_bytes()[authored["start_byte"]:authored["end_byte"]].decode()
    if selected != "Foo":
        raise GateError(f"overlap: second authored head span changed: {selected!r}")
    if "second_foo" not in diagnostic["message"]:
        raise GateError("overlap diagnostic does not identify the second stable rule")


def main() -> None:
    check_overlap()
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
    entry("tour-negatives", main, errors=(KeyError, TypeError))
