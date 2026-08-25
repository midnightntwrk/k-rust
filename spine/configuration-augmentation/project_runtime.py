#!/usr/bin/env python3
from __future__ import annotations
import argparse, json, re
from pathlib import Path

def cell(text: str, name: str) -> str | None:
    match = re.search(rf"<{name}>\s*(.*?)\s*</{name}>", text, re.DOTALL)
    if match is None: return None
    value = re.sub(r"\s+", " ", match.group(1)).strip()
    return re.sub(r"\s*~>\s*\.K$", "", value).strip()

parser = argparse.ArgumentParser()
parser.add_argument("input", type=Path); parser.add_argument("output", type=Path)
parser.add_argument("--erase-observation", action="store_true")
args = parser.parse_args(); text = args.input.read_text(encoding="utf-8")
result = {"k": cell(text,"k"), "state": cell(text,"state")}
if not args.erase_observation and cell(text,"observation") is not None: result["observation"] = cell(text,"observation")
args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n",encoding="utf-8")
