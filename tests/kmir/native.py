#!/usr/bin/env python3
"""Surface configuration and outcome reporting for the KMIR qualification corpus."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys
from typing import Any, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import GateError, behavior  # noqa: E402
from support.hashing import canonical_json, json_sha256  # noqa: E402
from support.pins import load_toml  # noqa: E402


def configuration_variables(case: Mapping[str, Any]) -> dict[str, str]:
    """Return surface configuration text for native and Java execution."""

    return {
        "PGM": "run",
        "PROGRAM": str(case["program"]),
        "LOCALS": str(case["locals"]),
        "RETVAL": "noReturn",
        "CURRENTFUNC": str(case.get("current_func", "ty(-1)")),
        "CALLER": str(case.get("caller", "ty(-1)")),
        "DEST": str(case.get("destination", "place(local(-1), .ProjectionElems)")),
        "TARGET": str(case.get("target", "noBasicBlockIdx")),
        "UNWIND": str(case.get("unwind", "unwindActionContinue")),
        "STACK": str(case.get("stack", ".List")),
        "FUNCTIONS": str(case.get("functions", ".Map")),
        "TYPES": str(case.get("types", ".Map")),
        "MEMORY": str(case.get("memory", ".Map")),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("krs_gate", type=Path)
    parser.add_argument("definition", type=Path)
    parser.add_argument("module")
    parser.add_argument("--definition-kore-sha256", required=True)
    parser.add_argument("corpus", type=Path)
    parser.add_argument("--outcomes", type=Path)
    parser.add_argument("--id", action="append", dest="case_ids")
    arguments = parser.parse_args()
    corpus = load_toml(arguments.corpus)
    cases = corpus.get("behavior")
    if not isinstance(cases, list) or not cases:
        raise GateError("behavior corpus is empty")
    if arguments.case_ids:
        requested = set(arguments.case_ids)
        cases = [case for case in cases if str(case.get("id")) in requested]
        missing = requested - {str(case["id"]) for case in cases}
        if missing:
            raise GateError(f"unknown behavior case ids: {sorted(missing)}")
    outcomes = behavior.native_corpus(
        arguments.krs_gate, arguments.definition, arguments.module, cases, configuration_variables, corpus,
        definition_kore_sha256=arguments.definition_kore_sha256,
    )
    digest = json_sha256(outcomes)
    if arguments.outcomes is not None:
        arguments.outcomes.write_text(canonical_json(outcomes) + "\n", encoding="utf-8")
    print(f"PASS native KMIR behavior: {len(outcomes)} executions; sha256={digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
