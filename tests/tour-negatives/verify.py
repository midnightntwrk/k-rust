#!/usr/bin/env python3
"""Pin the tour's focused negative diagnostics to exact authored tokens."""

from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
MACRO_NEGATIVES = ROOT / "crates" / "krs-macros" / "tests" / "fixtures" / "negative"


class GateError(RuntimeError):
    pass


def run(command: list[str], *, success: bool) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    candidates = []
    if configured := os.environ.get("KRS_Z3_LIB"):
        candidates.append(Path(configured))
    candidates.extend(Path("/nix/store").glob("*-z3-4.12.5-lib/lib"))
    z3 = next((path for path in candidates if path.joinpath("libz3.so").is_file()), None)
    if z3 is not None:
        for name in ("LD_LIBRARY_PATH", "LIBRARY_PATH"):
            env[name] = os.pathsep.join(
                value for value in (os.fspath(z3), env.get(name)) if value
            )
    result = subprocess.run(
        command,
        cwd=ROOT,
        env=env,
        capture_output=True,
        text=True,
        timeout=600,
        check=False,
    )
    if (result.returncode == 0) != success:
        output = "\n".join(part.strip() for part in (result.stdout, result.stderr) if part.strip())
        expectation = "succeed" if success else "fail"
        raise GateError(f"command should {expectation}: {' '.join(command)}\n{output[:3000]}")
    return result


def primary_error(output: str) -> dict[str, object]:
    for line in output.splitlines():
        try:
            message = json.loads(line)
        except json.JSONDecodeError:
            continue
        if message.get("reason") == "compiler-message":
            diagnostic = message["message"]
            if diagnostic.get("level") == "error":
                return diagnostic
    raise GateError("Cargo JSON contained no error diagnostic")


def check_rust_negative(binary: str, message: str, token: str) -> None:
    cargo = shutil.which("cargo")
    if cargo is None:
        raise GateError("cargo is unavailable")
    result = run(
        [
            cargo,
            "check",
            "--locked",
            "--offline",
            "--manifest-path",
            os.fspath(MACRO_NEGATIVES / "Cargo.toml"),
            "--bin",
            binary,
            "--message-format=json",
        ],
        success=False,
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
    cargo = shutil.which("cargo")
    if cargo is None:
        raise GateError("cargo is unavailable")
    run([cargo, "+stable", "build", "--locked", "-p", "krs-cli", "--bin", "krs"], success=True)
    executable = ROOT / "target" / "debug" / ("krs.exe" if os.name == "nt" else "krs")
    result = run(
        [
            os.fspath(executable),
            "check",
            "--manifest-path",
            os.fspath(HERE / "Cargo.toml"),
            "--package",
            "krs-tour-negatives",
            "--definition",
            "main",
        ],
        success=False,
    )
    lines = [line for line in result.stderr.splitlines() if line.startswith("{")]
    if len(lines) != 1:
        raise GateError(f"overlap: expected one JSON diagnostic line, got {len(lines)}")
    diagnostic = json.loads(lines[0])
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
            "renamed_krs::builtin::Map",
        ),
        (
            "initializer_control_flow",
            "unsupported declarative initializer body: statements, semicolons, control flow, mutation, and early return are forbidden",
            "if true { Self } else { Self }",
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
    try:
        main()
    except (GateError, OSError, KeyError, TypeError, ValueError, json.JSONDecodeError) as error:
        print(f"FAIL tour-negatives: {error}", file=sys.stderr)
        raise SystemExit(1) from error
    print("PASS tour-negatives")
