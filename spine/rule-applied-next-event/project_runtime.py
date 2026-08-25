#!/usr/bin/env python3
"""Project concrete k/state cells and an exact task-requested RuleApplied trace."""

import argparse
import json
import re
from pathlib import Path
from typing import Match


JSON_STRING = r'"(?:\\["\\/bfnrt]|\\u[0-9a-fA-F]{4}|[^"\\\x00-\x1f])*"'
EVENT = re.compile(
    rf"\s*ListItem\s*\(\s*ruleApplied\s*\(\s*ruleOrigin\s*\(\s*"
    rf"({JSON_STRING})\s*,\s*({JSON_STRING})\s*,\s*({JSON_STRING})\s*,\s*"
    rf"({JSON_STRING})\s*,\s*({JSON_STRING})\s*\)\s*\)\s*\)",
    re.S,
)


def fail(message: str) -> None:
    raise ValueError(message)


def decode_event(match: Match[str]) -> dict[str, object]:
    try:
        fields = [json.loads(value) for value in match.groups()]
    except json.JSONDecodeError as error:
        raise ValueError("invalid RuleOrigin JSON string") from error
    if not all(isinstance(value, str) for value in fields):
        fail("RuleOrigin field is not a string")
    return {
        "kind": "RuleApplied",
        "origin": dict(zip(
            ("id", "label", "module", "source", "location"), fields,
        )),
    }


def parse_trace(trace: str, event_count: int) -> list[dict[str, object]]:
    if event_count < 0:
        fail("event count is negative")
    events: list[dict[str, object]] = []
    position = 0
    while match := EVENT.match(trace, position):
        events.append(decode_event(match))
        position = match.end()
    if trace[position:].strip():
        fail("trace contains malformed or residual syntax")
    if len(events) != event_count:
        fail("unexpected exact RuleApplied event count")
    return events


def project(text: str, event_count: int, erase_trace: bool) -> dict[str, object]:
    result: dict[str, object] = {}
    for name in ("k", "state"):
        matches = re.findall(rf"<{name}>\s*(.*?)\s*</{name}>", text, re.S)
        if len(matches) != 1:
            fail(f"expected exactly one {name} cell")
        value = re.sub(r"\s+", " ", matches[0]).strip()
        if name == "k":
            value = re.sub(r"\s*~>\s*\.K$", "", value).strip()
        result[name] = value

    trace_matches = re.findall(r"<trace>\s*(.*?)\s*</trace>", text, re.S)
    if erase_trace:
        if len(trace_matches) > 1:
            fail("expected at most one trace cell while erasing")
    else:
        if len(trace_matches) != 1:
            fail("expected exactly one trace cell")
        result["trace"] = parse_trace(trace_matches[0], event_count)
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--event-count", type=int, required=True)
    parser.add_argument("--erase-trace", action="store_true")
    args = parser.parse_args()
    result = project(
        args.input.read_text(encoding="utf-8"), args.event_count, args.erase_trace,
    )
    args.output.write_text(
        json.dumps(result, sort_keys=True, indent=2) + "\n", encoding="utf-8",
    )


if __name__ == "__main__":
    main()
