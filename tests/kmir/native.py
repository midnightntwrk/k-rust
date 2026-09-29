#!/usr/bin/env python3
"""Surface configuration and expectations for the KMIR qualification corpus."""

from __future__ import annotations

import argparse
from pathlib import Path
import re
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


def normalize_term(value: str) -> str:
    """Keep the established whitespace normalization of outcome strings."""

    value = re.sub(r"\s+", " ", value.strip())
    value = re.sub(r"\s*([(),;:])\s*", r"\1", value)
    return re.sub(r"\.\s+", ".", value)


def expectations(case: Mapping[str, Any]) -> list[behavior.Expectation]:
    """Describe the final locals, return, body, stack, and computation cells."""

    expected = [
        behavior.Expectation("locals", text=str(case["expected_locals"])),
        behavior.Expectation("retVal", text=str(case["expected_return"])),
        behavior.Expectation("currentBody", size=int(case["expected_block_count"])),
        behavior.Expectation("stack", size=int(case.get("expected_stack_depth", 0))),
    ]
    if "expected_error" in case:
        expected.append(behavior.Expectation("k", head=f"#ProgramError({case['expected_error']})"))
    else:
        expected.append(behavior.Expectation("k", text=".K"))
    return expected


def outcome(case: Mapping[str, Any]) -> dict[str, Any]:
    """Return the established passing behavior outcome."""

    result: dict[str, Any] = {
        "id": str(case["id"]),
        "program": normalize_term(str(case["program"])),
        "block_count": int(case["expected_block_count"]),
        "locals": normalize_term(str(case["expected_locals"])),
        "stack_depth": int(case.get("expected_stack_depth", 0)),
        "return": normalize_term(str(case["expected_return"])),
    }
    if "expected_error" in case:
        result["error"] = normalize_term(str(case["expected_error"]))
    return result


SPEC = behavior.Specification(configuration_variables, expectations, outcome)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("krs_gate", type=Path)
    parser.add_argument("definition", type=Path)
    parser.add_argument("module")
    parser.add_argument("corpus", type=Path)
    parser.add_argument("--outcomes", type=Path)
    parser.add_argument("--id", action="append", dest="case_ids")
    arguments = parser.parse_args()
    cases = load_toml(arguments.corpus).get("behavior")
    if not isinstance(cases, list) or not cases:
        raise GateError("behavior corpus is empty")
    if arguments.case_ids:
        requested = set(arguments.case_ids)
        cases = [case for case in cases if str(case.get("id")) in requested]
        missing = requested - {str(case["id"]) for case in cases}
        if missing:
            raise GateError(f"unknown behavior case ids: {sorted(missing)}")
    outcomes = behavior.native_corpus(
        arguments.krs_gate, arguments.definition, arguments.module, cases, SPEC,
    )
    digest = json_sha256(outcomes)
    if arguments.outcomes is not None:
        arguments.outcomes.write_text(canonical_json(outcomes) + "\n", encoding="utf-8")
    print(f"PASS native KMIR behavior: {len(outcomes)} executions; sha256={digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
