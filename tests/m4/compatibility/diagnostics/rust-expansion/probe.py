#!/usr/bin/env python3
"""Require rustc's primary macro diagnostic to select the authored token."""

from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys


HERE = Path(__file__).resolve().parent
SOURCE = HERE / "src/lib.rs"
TOKEN = "syntax"


def expected_anchor() -> tuple[int, int, int]:
    source = SOURCE.read_text(encoding="utf-8")
    offset = source.index(TOKEN, source.index("#[k::constructor"))
    line = source.count("\n", 0, offset) + 1
    column = offset - source.rfind("\n", 0, offset)
    return line, column, len(TOKEN)


def main() -> int:
    environment = os.environ.copy()
    environment["CARGO_TARGET_DIR"] = "/tmp/krs-m4-diagnostics-rust-target"
    process = subprocess.run(
        [
            "cargo", "check", "--locked", "--manifest-path", str(HERE / "Cargo.toml"),
            "--message-format", "json",
        ],
        cwd=HERE,
        env=environment,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=180,
        check=False,
    )
    if process.returncode == 0:
        raise RuntimeError("malformed Rust-expansion fixture unexpectedly compiled")
    expected_line, expected_column, expected_length = expected_anchor()
    matches = []
    for line in process.stdout.splitlines():
        try:
            message = json.loads(line)
        except json.JSONDecodeError:
            continue
        if message.get("reason") != "compiler-message":
            continue
        diagnostic = message.get("message", {})
        if "missing required argument `sort = ...`" not in diagnostic.get("message", ""):
            continue
        for span in diagnostic.get("spans", []):
            if span.get("is_primary"):
                matches.append(span)
    if len(matches) != 1:
        raise RuntimeError(f"expected one primary malformed-attribute span, got {matches!r}")
    span = matches[0]
    actual = (span["line_start"], span["column_start"], span["column_end"] - span["column_start"])
    reported_path = Path(span["file_name"])
    if not reported_path.is_absolute():
        reported_path = HERE / reported_path
    if reported_path.resolve() != SOURCE or actual != (
        expected_line, expected_column, expected_length
    ):
        raise RuntimeError(f"diagnostic did not select exact authored token: {span!r}")
    print(f"PASS rust-expansion {SOURCE.name}:{expected_line}:{expected_column} `{TOKEN}`")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (RuntimeError, subprocess.TimeoutExpired) as error:
        print(f"FAIL rust-expansion: {error}", file=sys.stderr)
        raise SystemExit(1)
