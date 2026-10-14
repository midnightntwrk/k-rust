"""Helpers for querying and slicing the source artifacts KRS emits."""

from __future__ import annotations

from pathlib import Path
from typing import Mapping

from support import GateError, krs_gate


def emitted_files(directory: Path, gate: Path, *, environment: Mapping[str, str] | None = None) -> tuple[str, ...]:
    """Require the exact Rust-owned emit-k file set and ownership marker."""

    files = krs_gate.ir_query(gate, directory, {"kind": "files"}, environment=environment)
    if files["actual"] != files["expected"] or not files["owned"]:
        raise GateError(f"emit-k artifact set or ownership differs: {files!r}")
    return tuple(files["expected"])


def emitted_claims(
    directory: Path, module: str, expected: int, *, gate: Path,
    environment: Mapping[str, str] | None = None,
) -> tuple[list[str], str]:
    """Return claim labels in emission order and their exact generated block.

    The exact specification frame is a source-layout contract.
    Claim identity, count, order, and byte ranges come from the Rust query.
    """

    path = directory / "spec.k"
    if not path.is_file():
        raise GateError(f"emit-k wrote no spec.k in {directory}")
    source = path.read_bytes()
    header = f'requires "definition.k"\n\nmodule {module}-SPEC\n  imports {module}\n\n'.encode()
    footer = b"endmodule\n"
    if not source.startswith(header) or not source.endswith(footer):
        raise GateError(f"spec.k does not have the exact {module}-SPEC frame")
    rows = krs_gate.ir_query(
        gate, directory, {"kind": "sentences", "sentence_kind": "claim"}, environment=environment,
    )["rows"]
    labels = [row["label"] for row in rows]
    if len(labels) != expected or len(set(labels)) != expected:
        raise GateError(f"expected {expected} emitted claims with distinct labels, found {labels!r}")
    cursor = len(header)
    for row in rows:
        generated = row["generated"]
        if generated is None or generated["artifact"] != "spec.k" or generated["start_byte"] != cursor:
            raise GateError("spec.k claims do not form one contiguous generated block")
        cursor = generated["end_byte"]
    if cursor != len(source) - len(footer):
        raise GateError("spec.k holds more than its claim sentences")
    return labels, source[len(header):cursor].decode("utf-8")
