#!/usr/bin/env python3
"""Require a structured KRS analysis diagnostic at the second Collision."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[4]))
from support import GateError  # noqa: E402
from support.hashing import sha256_file  # noqa: E402
from support.process import run  # noqa: E402


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


def has_expected_range(envelope: dict[str, object]) -> bool:
    authored = envelope.get("authored_range")
    if not isinstance(authored, dict):
        return False
    file = authored.get("file")
    if not isinstance(file, dict):
        return False
    start, end, _, _, _ = expected_anchor()
    return (
        authored.get("start_byte") == start
        and authored.get("end_byte") == end
        and file.get("package_relative_path") == "src/lib.rs"
        and file.get("content_sha256") == sha256_file(SOURCE)
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--krs", type=Path, required=True)
    arguments = parser.parse_args()
    process = run(
        [
            arguments.krs, "check", "--manifest-path", HERE / "Cargo.toml",
            "--package", "krs-m4-diagnostic-analysis", "--definition", "main",
            "--backend", "llvm",
        ],
        environment={"CARGO_TARGET_DIR": "/tmp/krs-m4-diagnostics-analysis-target"},
        timeout=180,
        check=False,
    )
    output = "\n".join(part for part in (process.stdout, process.stderr) if part)
    if process.returncode == 0 or "emitted symbol name collision" not in output:
        raise GateError(f"fixture did not reach the intended collision: {output[:1200]}")
    if "/collectors/" in output or "target/krs/collectors" in output:
        raise GateError("diagnostic leaked a generated collector path")
    envelopes = []
    for line in output.splitlines():
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(value, dict) and value.get("stage") == "analysis":
            envelopes.append(value)
    start, end, line, column, length = expected_anchor()
    matching = [
        envelope for envelope in envelopes
        if envelope.get("code") == "symbol-name-collision" and has_expected_range(envelope)
    ]
    if len(matching) != 1:
        raise GateError(
            "collision lacks one stable analysis/code/authored-range envelope; "
            f"expected=src/lib.rs bytes {start}..{end} "
            f"(line {line}, columns {column}..{column + length})"
        )
    print(json.dumps(matching[0], sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except GateError as error:
        print(f"BLOCKED krs-analysis diagnostic: {error}", file=sys.stderr)
        raise SystemExit(1)
