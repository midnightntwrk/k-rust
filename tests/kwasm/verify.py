#!/usr/bin/env python3
"""Fail-closed qualification gate for the readable KWasm integer slice."""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys
import tempfile
from typing import Any, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError, semantics  # noqa: E402
from support.hashing import json_sha256  # noqa: E402
from support.lock import descriptor_protocol, k_version  # noqa: E402
from support.pins import Ledger, load_toml  # noqa: E402
from support.process import run  # noqa: E402
from support.tools import k_tool, scratch_root  # noqa: E402


PORT = semantics.Port(
    label="KWasm",
    key="kwasm",
    checkout=ROOT.parent / "inspirations/runtimeverification/wasm-semantics",
    descriptors=60,
)


def java_reference_gate(
    workspace: Path,
    artifacts: Path,
    k: Mapping[str, str],
    pins: Ledger,
    corpus: Mapping[str, Any],
) -> tuple[int, int]:
    definition, source, claims = semantics.reference_definition(
        PORT, workspace, artifacts, k["kompile"], 1, pins
    )

    behavior = corpus.get("behavior")
    if not isinstance(behavior, list) or not behavior:
        raise GateError("behavior corpus is empty")
    outcomes: list[dict[str, str]] = []
    for case in behavior:
        case_id = str(case["id"])
        expected_outcome = str(case.get("expected_outcome", "value"))
        if expected_outcome not in {"trap", "value"}:
            raise GateError(f"{case_id} has an unsupported expected outcome")
        result = run(
            [
                k["krun"],
                "--definition",
                definition,
                f"-cPGM={case['program']}",
                "-cSTACK=.ValStack",
                "--output",
                "pretty",
            ],
            timeout=120,
        ).stdout
        if expected_outcome == "trap":
            if not re.search(
                r"<instrs>\s*trap\s*~>\s*\.Instrs\s*~>\s*\.K\s*</instrs>",
                result,
            ):
                raise GateError(f"{case_id} did not finish with a trap: {result}")
            if not re.search(r"<valstack>\s*\.ValStack\s*</valstack>", result):
                raise GateError(f"{case_id} trapped with an unexpected stack: {result}")
            observed = {"id": case_id, "outcome": "trap"}
            expected = {"id": case_id, "outcome": "trap"}
        else:
            if not re.search(r"<instrs>\s*\.K\s*</instrs>", result):
                raise GateError(
                    f"{case_id} did not finish its instruction stream: {result}"
                )
            match = re.search(
                r"<valstack>\s*<\s*(i32|i64)\s*>\s*(-?[0-9]+)\s*:\s*\.ValStack\s*</valstack>",
                result,
            )
            if match is None:
                raise GateError(f"{case_id} has an unexpected value stack: {result}")
            observed = {
                "id": case_id,
                "outcome": "value",
                "type": match.group(1),
                "value": match.group(2),
            }
            expected = {
                "id": case_id,
                "outcome": "value",
                "type": str(case["expected_type"]),
                "value": str(case["expected_value"]),
            }
        if observed != expected:
            raise GateError(f"{case_id} differs: expected={expected}, actual={observed}")
        outcomes.append(observed)
    pins.expect("behavior_sha256", json_sha256(outcomes))

    semantics.reference_proof(PORT, workspace, definition, source, claims, k["kprove"])
    return len(outcomes), 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--java-reference",
        action="store_true",
        help="also run the pinned K toolchain behavior comparison and proof",
    )
    parser.add_argument(
        "--record",
        action="store_true",
        help="run the gate and rewrite the output pins it measured",
    )
    semantics.add_artifacts_only_argument(parser)
    arguments = parser.parse_args()
    semantics.reject_artifacts_only_conflicts(parser, arguments)
    pins = Ledger(PORT.pins_path, record=arguments.record, artifacts_only=arguments.artifacts_only)
    corpus = load_toml(PORT.corpus_path)
    environment = semantics.preflight(PORT, pins, corpus)
    with tempfile.TemporaryDirectory(prefix="krs-kwasm-gate-", dir=scratch_root()) as temporary:
        workspace = Path(temporary)
        krs, compiler, runner = semantics.rust_gate(PORT, environment)
        artifacts = semantics.artifact_gate(PORT, workspace, krs, pins, environment)
        definition = semantics.native_definition(workspace, artifacts, compiler, pins, environment)
        if arguments.artifacts_only:
            print(f"PASS readable KWasm integer slice: {semantics.artifacts_only_summary(PORT)}")
            return 0
        behavior_count = semantics.native_behavior(PORT, runner, definition, pins, corpus, environment)
        proof_count = 0
        if arguments.java_reference:
            k = {name: k_tool(name, k_version()) for name in ("kompile", "krun", "kprove")}
            reference_behavior, proof_count = java_reference_gate(
                workspace, artifacts, k, pins, corpus
            )
            if reference_behavior != behavior_count:
                raise GateError("K-Rust and reference execution counts differ")
    pins.finish("readable KWasm integer slice")
    proof_status = (
        f"{proof_count} reference proof"
        if arguments.java_reference
        else "1 reference proof deferred to --java-reference"
    )
    print(
        "PASS readable KWasm integer slice: "
        f"{PORT.descriptors} descriptors; {behavior_count} K-Rust executions; {proof_status}; "
        f"protocol {descriptor_protocol()}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (GateError, OSError) as error:
        print(f"FAIL readable KWasm integer slice: {error}", file=sys.stderr)
        raise SystemExit(1)
