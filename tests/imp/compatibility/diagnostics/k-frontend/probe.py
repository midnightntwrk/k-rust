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
from support import GateError, krs_gate  # noqa: E402
from support.kdefinition import emitted_claims  # noqa: E402
from support.tools import checkout_scratch, z3_environment  # noqa: E402
from support.process import run  # noqa: E402


LOCATION = re.compile(r"Location\((\d+),(\d+),(\d+),(\d+)\)")
EMITTED_CLAIMS = 20


def exact_mapping(
    gate: Path, artifacts: Path, authored: Path, source_relative_path: str, token: str,
) -> tuple[dict[str, object], dict[str, object]]:
    mapping = krs_gate.ir_query(gate, artifacts, {
        "kind": "source_token", "artifact": "spec.k", "authored": str(authored),
        "package_relative_path": source_relative_path, "token": token,
    }, environment=z3_environment())
    return mapping["authored_range"], mapping["generated"]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--spec", type=Path, required=True, help="emitted spec.k beside definition.k")
    parser.add_argument("--sources", type=Path, required=True)
    parser.add_argument("--authored", type=Path, required=True)
    parser.add_argument("--source-relative-path", required=True)
    parser.add_argument("--token", required=True)
    parser.add_argument("--kompile")
    parser.add_argument("--module")
    parser.add_argument("--verification-definition", type=Path)
    arguments = parser.parse_args()
    spec = arguments.spec.read_bytes()
    gate = krs_gate.configured_or_build(checkout_scratch() / "imp-gate-root-target")
    if arguments.sources.resolve() != arguments.spec.with_name("sources.json").resolve():
        raise GateError("--sources must name the emitted spec's sources.json")
    origin, generated = exact_mapping(
        gate, arguments.spec.parent, arguments.authored, arguments.source_relative_path, arguments.token,
    )
    start, end = int(generated["start_byte"]), int(generated["end_byte"])
    artifact_line = generated["start_line"]
    artifact_column = generated["start_column"]
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

    _, claims_text = emitted_claims(arguments.spec.parent, arguments.module, EMITTED_CLAIMS, gate=gate, environment=z3_environment())
    execution = arguments.spec.with_name("definition.k").read_bytes()
    claims = claims_text.encode("utf-8")
    mapped = spec[start:end]
    claim_rows = krs_gate.ir_query(gate, arguments.spec.parent, {
        "kind": "sentences", "sentence_kind": "claim",
    }, environment=z3_environment())["rows"]
    block_start = claim_rows[0]["generated"]["start_byte"]
    claim_start = start - block_start
    if not 0 <= claim_start < claim_start + end - start <= len(claims):
        raise GateError("mapped byte range is outside the emitted claims block")
    if claims[claim_start:claim_start + len(mapped)] != mapped:
        raise GateError("mapped bytes differ from the generated claims slice")
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
