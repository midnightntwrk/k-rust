#!/usr/bin/env python3
"""Project the two concrete runtime cells and one exact RuleApplied event."""

import argparse
import json
import re
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("input", type=Path)
parser.add_argument("output", type=Path)
parser.add_argument("--erase-trace", action="store_true")
args = parser.parse_args()
text = args.input.read_text(encoding="utf-8")
result: dict[str, object] = {}
for name in ("k", "state"):
    match = re.search(rf"<{name}>\s*(.*?)\s*</{name}>", text, re.S)
    if match:
        value = re.sub(r"\s+", " ", match.group(1)).strip()
        if name == "k":
            value = re.sub(r"\s*~>\s*\.K$", "", value).strip()
        result[name] = value

trace_match = re.search(r"<trace>\s*(.*?)\s*</trace>", text, re.S)
if trace_match and not args.erase_trace:
    trace = trace_match.group(1).strip()
    if trace == ".List":
        result["trace"] = []
    else:
        if len(re.findall(r"\bruleApplied\s*\(", trace)) != 1:
            raise ValueError("expected one RuleApplied event")
        if len(re.findall(r"\bruleOrigin\s*\(", trace)) != 1:
            raise ValueError("expected one RuleOrigin payload")
        encoded_fields = re.findall(r'"(?:\\.|[^"\\])*"', trace)
        fields = [json.loads(value) for value in encoded_fields]
        if len(fields) != 5:
            raise ValueError(f"expected five RuleOrigin fields, found {len(fields)}")
        result["trace"] = [
            {
                "kind": "RuleApplied",
                "origin": dict(zip(("id", "label", "module", "source", "location"), fields)),
            }
        ]

args.output.write_text(
    json.dumps(result, sort_keys=True, indent=2) + "\n", encoding="utf-8"
)
