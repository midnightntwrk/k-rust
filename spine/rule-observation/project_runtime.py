#!/usr/bin/env python3
import argparse
import json
import re
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("input", type=Path)
parser.add_argument("output", type=Path)
parser.add_argument("--erase-observation", action="store_true")
args = parser.parse_args()
text = args.input.read_text(encoding="utf-8")
result = {}
for name in ("k", "state", "observation"):
    match = re.search(rf"<{name}>\s*(.*?)\s*</{name}>", text, re.S)
    if match:
        value = re.sub(r"\s+", " ", match.group(1)).strip()
        if name == "k":
            value = re.sub(r"\s*~>\s*\.K$", "", value).strip()
        result[name] = value
if args.erase_observation:
    result.pop("observation", None)
args.output.write_text(json.dumps(result, sort_keys=True, indent=2) + "\n", encoding="utf-8")
