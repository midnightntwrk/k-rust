#!/usr/bin/env python3
"""Map one induced K frontend Location through sources.json, without guessing."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[4]))
from support import GateError  # noqa: E402
from support.hashing import sha256_bytes  # noqa: E402
from support.kdefinition import split_claims  # noqa: E402
from support.process import run  # noqa: E402


LOCATION = re.compile(r"Location\((\d+),(\d+),(\d+),(\d+)\)")
EMITTED_CLAIMS = 20


def ranged_origins(entry: dict[str, object]) -> list[dict[str, object]]:
    result = []
    for frame in entry.get("origin", []):
        if isinstance(frame, dict) and frame.get("frame_type") == "ranged" and frame.get("kind") == "authored":
            value = frame.get("range")
            if isinstance(value, dict):
                result.append(value)
    return result


def exact_mapping(
    definition: bytes, sidecar: dict[str, object], source: bytes, source_relative_path: str, token: str
) -> tuple[dict[str, object], dict[str, object]]:
    matches = []
    for entry in sidecar.get("entries", []):
        if not isinstance(entry, dict) or not isinstance(entry.get("generated"), dict):
            continue
        generated = entry["generated"]
        origins = ranged_origins(entry)
        if len(origins) != 1:
            continue
        origin = origins[0]
        file = origin.get("file", {})
        if not isinstance(file, dict) or file.get("package_relative_path") != source_relative_path:
            continue
        if file.get("content_sha256") != sha256_bytes(source):
            continue
        start, end = int(origin["start_byte"]), int(origin["end_byte"])
        generated_start, generated_end = int(generated["start_byte"]), int(generated["end_byte"])
        if (
            0 <= start < end <= len(source)
            and 0 <= generated_start < generated_end <= len(definition)
            and generated.get("artifact") == "definition.k"
            and source[start:end].decode() == token
            and definition[generated_start:generated_end]
        ):
            matches.append((origin, generated))
    if len(matches) != 1:
        raise GateError(f"expected one exact sidecar mapping for {token!r}, got {len(matches)}")
    return matches[0]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--definition", type=Path, required=True)
    parser.add_argument("--sources", type=Path, required=True)
    parser.add_argument("--authored", type=Path, required=True)
    parser.add_argument("--source-relative-path", required=True)
    parser.add_argument("--token", required=True)
    parser.add_argument("--kompile")
    parser.add_argument("--module")
    parser.add_argument("--verification-definition", type=Path)
    arguments = parser.parse_args()
    definition = arguments.definition.read_bytes()
    source = arguments.authored.read_bytes()
    sidecar = json.loads(arguments.sources.read_text(encoding="utf-8"))
    origin, generated = exact_mapping(
        definition, sidecar, source, arguments.source_relative_path, arguments.token
    )
    start, end = int(generated["start_byte"]), int(generated["end_byte"])
    artifact_line = definition[:start].count(b"\n") + 1
    artifact_column = start - definition.rfind(b"\n", 0, start)
    if not arguments.kompile:
        print(json.dumps({
            "artifact_generated_location": [artifact_line, artifact_column],
            "authored_range": origin,
        }, sort_keys=True))
        return 0
    if not arguments.module:
        raise GateError("--module is required with --kompile")
    if arguments.verification_definition is None:
        raise GateError("--verification-definition is required with --kompile")
    verification_definition = arguments.verification_definition.resolve()
    if not verification_definition.joinpath("imp-verification.k").is_file():
        raise GateError("verification definition lacks imp-verification.k")

    execution_text, _, claims_text = split_claims(definition.decode("utf-8"), EMITTED_CLAIMS)
    execution, claims = execution_text.encode("utf-8"), claims_text.encode("utf-8")
    mapped = definition[start:end]
    if not mapped or claims.count(mapped) != 1:
        raise GateError("mapped generated range is not unique in emitted claims")
    claim_start = claims.index(mapped)
    broken_claims = claims[:claim_start] + b"+" + claims[claim_start + len(mapped):]
    spec_module = f"{arguments.module}-DIAGNOSTIC-SPEC"
    spec_header = (
        b'requires "execution.k"\n'
        b'requires "imp-verification.k"\n\n'
        + f"module {spec_module}\n".encode()
        + f"  imports {arguments.module}\n".encode()
        + b"  imports IMP-VERIFICATION-SYNTAX\n\n"
    )
    broken = spec_header + broken_claims + b"endmodule\n"
    generated_start = len(spec_header) + claim_start
    line = broken[:generated_start].count(b"\n") + 1
    column = generated_start - broken.rfind(b"\n", 0, generated_start)
    with tempfile.TemporaryDirectory(prefix="krs-imp-frontend-diagnostic-") as temporary:
        temporary = Path(temporary)
        (temporary / "execution.k").write_bytes(execution)
        broken_path = temporary / "spec.k"
        broken_path.write_bytes(broken)
        process = run(
            [arguments.kompile, broken_path, "-I", temporary,
             "-I", verification_definition, "--main-module", spec_module,
             "--syntax-module", spec_module, "--backend", "llvm",
             "--output-definition", temporary / "out"],
            timeout=180,
            check=False,
        )
    locations = [tuple(map(int, match.groups())) for match in LOCATION.finditer(process.stderr)]
    if process.returncode == 0 or not any(location[:2] == (line, column) for location in locations):
        raise GateError("K frontend failure did not select the exact induced generated range")
    print(json.dumps({
        "artifact_generated_location": [artifact_line, artifact_column],
        "authored_range": origin,
        "frontend_spec_location": [line, column],
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
