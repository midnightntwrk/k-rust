#!/usr/bin/env python3
"""Fail-closed qualification gate for the readable KWasm integer slice."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys
import tempfile
from typing import Any, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError, semantics  # noqa: E402
from support.kdefinition import parse_kore_pattern  # noqa: E402
from support.lock import k_version, krs_ir_schema  # noqa: E402
from support.pins import Ledger, load_toml  # noqa: E402
from support.process import run  # noqa: E402
from support.tools import k_tool, scratch_root  # noqa: E402
from kwasm import native  # noqa: E402


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
    native_outcomes: list[dict[str, Any]],
) -> int:
    definition, source, claims = semantics.reference_definition(
        PORT, workspace, artifacts, k["kompile"], 1, pins
    )

    behavior = corpus.get("behavior")
    if not isinstance(behavior, list) or not behavior:
        raise GateError("behavior corpus is empty")
    outcomes: list[dict[str, str]] = []
    for case in behavior:
        result = run(
            [
                k["krun"],
                "--definition",
                definition,
                f"-cPGM={case['program']}",
                "-cSTACK=.ValStack",
                "--output",
                "kore",
            ],
            timeout=120,
        ).stdout
        state = parse_kore_pattern(result)
        outcomes.append(native.observed(case, state))

    semantics.compare_routes(PORT.label, native_outcomes, outcomes, {})
    cases_by_id = {str(case["id"]): case for case in behavior}
    for outcome in outcomes:
        native.checked(cases_by_id[str(outcome["id"])], outcome)

    semantics.reference_proof(PORT, workspace, definition, source, claims, k["kprove"])
    return 1


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
        behavior_count, native_outcomes = semantics.native_behavior(PORT, runner, definition, pins, corpus, environment)
        proof_count = 0
        if arguments.java_reference:
            k = {name: k_tool(name, k_version()) for name in ("kompile", "krun", "kprove")}
            proof_count = java_reference_gate(
                workspace, artifacts, k, pins, corpus
            )
    pins.finish("readable KWasm integer slice")
    proof_status = (
        f"{proof_count} reference proof"
        if arguments.java_reference
        else "1 reference proof deferred to --java-reference"
    )
    print(
        "PASS readable KWasm integer slice: "
        f"{PORT.descriptors} descriptors; {behavior_count} K-Rust executions; {proof_status}; "
        f"KRS schema {krs_ir_schema()}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (GateError, OSError) as error:
        print(f"FAIL readable KWasm integer slice: {error}", file=sys.stderr)
        raise SystemExit(1)
