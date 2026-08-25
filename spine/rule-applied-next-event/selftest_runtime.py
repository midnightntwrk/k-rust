#!/usr/bin/env python3
"""Adversarial zero-backend checks for exact pretty-runtime projection."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Callable

import project_runtime as projector


def expect_error(name: str, operation: Callable[[], object],
                 results: list[dict[str, object]]) -> None:
    try:
        operation()
    except ValueError:
        results.append({"case": name, "classification": "error", "rejected": True})
        return
    raise SystemExit(f"runtime self-test unexpectedly accepted {name}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("valid_runtime", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    valid_text = args.valid_runtime.read_text(encoding="utf-8")
    valid = projector.project(valid_text, 2, False)
    trace = valid["trace"]
    if not isinstance(trace, list) or len(trace) != 2:
        raise SystemExit("valid runtime did not project to an exact pair")

    start = valid_text.index("<trace>") + len("<trace>")
    end = valid_text.index("</trace>")
    prefix, suffix = valid_text[:start], valid_text[end:]
    origin = ('ruleOrigin ( "id" , "label" , "module" , "source" , '
              '"location" )')
    detached = (f"{prefix}\nruleApplied ( .K ) ruleApplied ( .K )\n"
                f"{origin} {origin}\n{suffix}")
    residual = valid_text[:end] + "\n.List\n" + valid_text[end:]
    malformed_wrapper = valid_text.replace("ListItem ( ruleApplied", "ruleApplied", 1)
    first_event = projector.EVENT.match(valid_text[start:end])
    if first_event is None:
        raise SystemExit("valid runtime does not start with a structural event")
    wrong_count = prefix + first_event.group(0) + "\n" + suffix

    results: list[dict[str, object]] = []
    for name, text in (
        ("detached event and origin terms", detached),
        ("residual trace syntax", residual),
        ("missing ListItem wrapper", malformed_wrapper),
        ("wrong exact event count", wrong_count),
    ):
        expect_error(name, lambda value=text: projector.project(value, 2, False), results)

    output = {
        "verdict": "pass",
        "classification": "runtime projection errors, never synthesized events",
        "compilerBackendInvocations": 0,
        "caseCount": len(results),
        "validExactEventCount": 2,
        "cases": sorted(results, key=lambda item: str(item["case"])),
    }
    args.output.write_text(
        json.dumps(output, sort_keys=True, indent=2) + "\n", encoding="utf-8",
    )


if __name__ == "__main__":
    main()
