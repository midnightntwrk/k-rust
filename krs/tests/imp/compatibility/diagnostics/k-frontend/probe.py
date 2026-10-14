#!/usr/bin/env python3
"""Map one induced K frontend Location through sources.json, without guessing.

With `--frontend`, the induced `kompile` failure forms the reference snapshot
`imp/frontend-diagnostic`, keyed by the digests of the emitted `definition.k`
and of the mutated spec. It replays the reference cache entry that
`--reference-sha256` names; a cache miss or `--refresh-reference` runs
`kompile` live instead.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[4]))
from support import ROOT, GateError, krs_gate  # noqa: E402
from support.kdefinition import emitted_claims  # noqa: E402
from support.reference import (  # noqa: E402
    Key, Snapshot, add_child_arguments, add_refresh_argument,
)
from support.tools import z3_environment  # noqa: E402


LOCATION = re.compile(r"Location\((\d+),(\d+),(\d+),(\d+)\)")
EMITTED_CLAIMS = 20


def frontend_key(definition: Path) -> Key:
    """The snapshot key: the emitted definition the spec requires.

    The spec reads nothing upstream: the emitted claims spell every `Id` token
    as `#token`, so they need no upstream `Id` syntax.
    """

    return Key(tools=("kompile",), inputs={"emitted/definition.k": definition})


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
    parser.add_argument(
        "--frontend", action="store_true",
        help="also require K's frontend Location for an induced spec failure",
    )
    parser.add_argument("--module")
    add_refresh_argument(parser)
    add_child_arguments(parser)
    arguments = parser.parse_args()
    spec = arguments.spec.read_bytes()
    gate = krs_gate.configured_or_build()
    if arguments.sources.resolve() != arguments.spec.with_name("sources.json").resolve():
        raise GateError("--sources must name the emitted spec's sources.json")
    origin, generated = exact_mapping(
        gate, arguments.spec.parent, arguments.authored, arguments.source_relative_path, arguments.token,
    )
    start, end = int(generated["start_byte"]), int(generated["end_byte"])
    artifact_line = generated["start_line"]
    artifact_column = generated["start_column"]
    if not arguments.frontend:
        print(json.dumps({
            "artifact_generated_location": [artifact_line, artifact_column],
            "authored_range": origin,
        }, sort_keys=True))
        return 0
    if not arguments.module:
        raise GateError("--module is required with --frontend")

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
        b'requires "execution.k"\n\n'
        + f"module {spec_module}\n".encode()
        + f"  imports {arguments.module}\n\n".encode()
    )
    broken = spec_header + broken_claims + b"endmodule\n"
    generated_start = len(spec_header) + claim_start
    line = broken[:generated_start].count(b"\n") + 1
    column = generated_start - broken.rfind(b"\n", 0, generated_start)
    refresh = arguments.refresh_reference
    with tempfile.TemporaryDirectory(prefix="krs-imp-frontend-diagnostic-") as temporary:
        temporary = Path(temporary)
        (temporary / "execution.k").write_bytes(execution)
        broken_path = temporary / "spec.k"
        broken_path.write_bytes(broken)
        k = Snapshot(
            "imp/frontend-diagnostic", frontend_key(temporary / "execution.k"), workspace=temporary,
            refresh=refresh, expected=arguments.reference_sha256, staging=arguments.reference_staging,
        )
        process = k.run(
            "kompile/induced-spec-error", "kompile",
            [broken_path, "-I", temporary, "--main-module", spec_module,
             "--syntax-module", spec_module, "--backend", "llvm",
             "--output-definition", temporary / "out"],
            timeout=180,
        )
    locations = [tuple(map(int, match.groups())) for match in LOCATION.finditer(process.stderr)]
    if process.returncode == 0 or not any(location[:2] == (line, column) for location in locations):
        raise GateError("K frontend failure did not select the exact induced generated range")
    # Only a passing check completes the snapshot, so a failing live run
    # stages nothing for the calling gate to store.
    k.finish()
    print(json.dumps({
        "artifact_generated_location": [artifact_line, artifact_column],
        "authored_range": origin,
        "frontend_spec_location": [line, column],
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
