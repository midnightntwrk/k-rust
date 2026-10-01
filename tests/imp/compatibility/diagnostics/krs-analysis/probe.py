#!/usr/bin/env python3
"""Require a structured KRS analysis diagnostic at the second Collision."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[4]))
from support import GateError  # noqa: E402
from support.diagnostics import KrsDiagnostic, krs_diagnostics  # noqa: E402
from support.hashing import sha256_file  # noqa: E402
from support.krs import Invocation  # noqa: E402
from support.process import run  # noqa: E402
from support.tools import checkout_scratch  # noqa: E402


HERE = Path(__file__).resolve().parent
SOURCE = HERE / "src/lib.rs"
TOKEN = "Collision"


def expected_anchor() -> tuple[int, int, int, int, int]:
    source = SOURCE.read_bytes()
    text = source.decode("utf-8")
    first = text.index("pub struct Collision")
    offset = text.index(TOKEN, text.index("pub struct Collision", first + 1))
    line = text.count("\n", 0, offset) + 1
    column = offset - text.rfind("\n", 0, offset)
    return offset, offset + len(TOKEN), line, column, len(TOKEN)


def has_expected_range(diagnostic: KrsDiagnostic) -> bool:
    authored = diagnostic.authored_range
    if authored is None:
        return False
    start, end, _, _, _ = expected_anchor()
    return (
        authored.start_byte == start
        and authored.end_byte == end
        and authored.package_relative_path == "src/lib.rs"
        and authored.content_sha256 == sha256_file(SOURCE)
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--krs", type=Path, required=True)
    arguments = parser.parse_args()
    process = run(
        Invocation(arguments.krs, HERE / "Cargo.toml", "krs-imp-diagnostic-analysis", "main").argv(
            "check", "--backend", "llvm"
        ),
        environment={
            "CARGO_TARGET_DIR": os.fspath(
                Path(os.environ.get("KRS_IMP_PROBE_TARGET_ROOT", checkout_scratch()))
                / "krs-analysis"
            )
        },
        timeout=180,
        check=False,
    )
    output = "\n".join(part for part in (process.stdout, process.stderr) if part)
    if process.returncode == 0 or "emitted symbol name collision" not in output:
        raise GateError(f"fixture did not reach the intended collision: {output[:1200]}")
    if "/collectors/" in output or "target/krs/collectors" in output:
        raise GateError("diagnostic leaked a generated collector path")
    diagnostics = [
        value for value in krs_diagnostics(output)
        if value.stage == "analysis"
    ]
    start, end, line, column, length = expected_anchor()
    matching = [
        diagnostic for diagnostic in diagnostics
        if diagnostic.code == "krs::analysis::symbol-name-collision" and has_expected_range(diagnostic)
    ]
    if len(matching) != 1:
        raise GateError(
            "collision lacks one stable analysis/code/authored-range envelope; "
            f"expected=src/lib.rs bytes {start}..{end} "
            f"(line {line}, columns {column}..{column + length})"
        )
    print(matching[0].raw_json)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except GateError as error:
        print(f"BLOCKED krs-analysis diagnostic: {error}", file=sys.stderr)
        raise SystemExit(1)
